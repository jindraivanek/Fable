module rec Fable2OCaml

open Fable.AST
open Fable.AST.Fable

let nl = System.Environment.NewLine

let surround head tail body = head + body + tail
let par x = surround "(" ")" x

let delim sep xs = xs |> String.concat sep

let multi f = function
    | x::(y::tl) as xs -> f xs
    | [x] -> x
    | [] -> f []

let delimSurround sep head tail xs = xs |> (delim sep >> surround head tail)

let rec getTyp =
    function
    | Unit -> "unit"
    | Boolean -> "bool"
    | Char -> "char"
    | String -> "string"
    | Number kind ->
        match kind with
        | Int8 | Int16 | Int32 -> "int" | UInt8 | UInt16  | UInt32 -> "uint" | Float32 | Float64 -> "float" | Decimal -> "decimal"
    | EnumType (_, x) -> x
    | Option t -> getTyp t + " option" 
    | Tuple(ts) -> ts |> Seq.map getTyp |> delim " * " |> surround "(" ")"
    | Array t -> getTyp t + " array"
    | List t -> getTyp t + " list"
    | FunctionType(LambdaType t1, t2) -> [t1; t2] |> Seq.map getTyp |> delim " -> "
    | FunctionType(DelegateType ts, t) -> ts @ [t] |> Seq.map getTyp |> delim " -> "
    | GenericParam x -> x
    | DeclaredType (_, genericArgs) -> genericArgs |> List.map getTyp |> delim " "
    
    | MetaType
    | Any
    | Regex
    | ErasedUnion _ as x -> sprintf "%A" x
    
let letBind name e = sprintf "let %s = %s" name (getExpr e)

let rec getDecl =
    function
    | ActionDeclaration e -> getExpr e
    | ValueDeclaration (e, info) -> letBind info.Name e
    //| ConstructorDeclaration kind ->
    //| AttachedMemberDeclaration of args: Ident list * body: Expr * AttachedMemberDeclarationInfo
    | x -> sprintf "%A" x

// let rec getMatch (p, whenE, e) =
//     let whenClause = whenE |> Option.map (fun x -> " when " + getExpr x) |> Option.fill ""
//     [getPat p + whenClause; getExpr e] |> delim " -> "
 
// and getBind isRec isFirstRec (p, e) =
//     match isRec, isFirstRec with
//     | true, true -> "let rec "
//     | true, false -> "and "
//     | _ -> "let " 
//     + getPat p + " = " + nl + getExpr e

let getValue =
    function
    | UnitConstant -> "()"
    | BoolConstant b -> sprintf "%b" b
    | CharConstant c -> sprintf "%c" c
    | StringConstant s -> s
    | NumberConstant (x, kind) ->
        match kind with
        | Int8 | Int16 | Int32 -> sprintf "%i" (int x) 
        | UInt8 | UInt16  | UInt32 -> sprintf "%u" (int x) 
        | Float32 | Float64 -> sprintf "%f" x 
        //| Decimal -> sprintf "%M" (decimal x)
    | Enum (_, x) -> x
    | NewOption (value, t) -> value |> Option.map (fun e -> "Some " + getExpr e |> par) |> Option.defaultValue "None"
    | NewArray (ArrayValues vals, t) -> vals |> Seq.map getExpr |> delim ", " |> surround "[|" "|]"
    | NewArray (ArrayAlloc e, t) -> sprintf "Array.create %s" <| getExpr e
    | NewList (Some (hd, e), t) -> sprintf "%s :: %s" (getExpr hd) (getExpr e)
    | NewList (None, t) -> "[]"
    | NewTuple es -> es |> Seq.map getExpr |> delim ", " |> surround "(" ")"
    | NewRecord (es, entity, ts) -> 
        Seq.zip es entity.FSharpFields |> Seq.map (fun (e,f) -> sprintf "%s = %s" f.Name (getExpr e)) 
        |> delimSurround ";" "{" "}"
    | NewUnion _
    | NewErasedUnion _
    | Null _
    | TypeInfo _
    | RegexConstant _ as x -> sprintf "%A" x
    
let getExpr =
    function
    | Value kind -> getValue kind 
    | IdentExpr ident -> ident.Name
    /// Some expressions must be resolved in the last pass for better optimization (e.g. list to seq cast)
    //| DelayedResolution of DelayedResolutionKind * Type * SourceLocation option
    //| Import of selector: Expr * path: Expr * ImportKind * Type * SourceLocation option

    | Function of FunctionKind * body: Expr * name: string option
    | ObjectExpr of ObjectMember list * Type * baseCall: Expr option

    | Test of Expr * TestKind * range: SourceLocation option
    | Operation of OperationKind * typ: Type * range: SourceLocation option
    | Get of Expr * GetKind * typ: Type * range: SourceLocation option

    | Debugger
    | Throw of Expr * typ: Type * range: SourceLocation option

    | DecisionTree of Expr * targets: (Ident list * Expr) list
    | DecisionTreeSuccess of targetIndex: int * boundValues: Expr list * Type

    | Sequential of Expr list
    | Let of bindings: (Ident * Expr) list * body: Expr
    | Set of Expr * SetKind * value: Expr * range: SourceLocation option
    // TODO: Check if we actually need range for loops
    | Loop of LoopKind * range: SourceLocation option
    | TryCatch of body: Expr * catch: (Ident * Expr) option * finalizer: Expr option
    | IfThenElse of guardExpr: Expr * thenExpr: Expr * elseExpr: Expr

    | ExprConst (ConstId c) -> c
    | ExprVal (ValId v) -> v
    | ExprApp (e1, e2) -> [getExpr e1; getExpr e2] |> delim " " |> surround "(" ")"
    | ExprInfixApp (e1, ValId v, e2) -> [getExpr e1; v; getExpr e2] |> delim " " |> surround "(" ")"
    | ExprTuple ts -> ts |> List.map getExpr |> delimSurround ", " "(" ")"
    | ExprList ts -> ts |> List.map getExpr |> delimSurround "; " "[" "]"
    | ExprRecord (copyE, rows) -> 
        let fields = rows |> Seq.map (fun (FieldId f, e) -> f + " = " + getExpr e) |> delim "; " 
        let copyStat = copyE |> Option.map (fun x -> getExpr x + " with ") |> Option.fill ""
        copyStat + fields |> surround "{" "}"
    | ExprBind (_,p,e) -> 
        getBind false false (p,e)
    | ExprRecBind bindings -> 
        let n = Seq.length bindings
        (bindings |> Seq.mapi (fun i x -> getBind true (i=0) x) |> delim nl) 
    | ExprMatch (e, rows) -> 
        (["match"; getExpr e; "with"] |> delim " ")
        + nl + (rows |> Seq.map (fun m -> getMatch m) |> delim (nl + "| "))
    | ExprMatchLambda (rows) -> 
        "function"
        + nl + (rows |> Seq.map (fun m -> getMatch m) |> delim (nl + "| "))
    | ExprLambda (args, e) -> "fun " + (args |> Seq.map getPat |> delim " ") + " -> " + getExpr e |> surround "(" ")"
    | ExprWithType (t, e) -> getExpr e + " : " + getTyp t
    | ExprModule (ModuleId m, e) -> "module " + m + " = struct " + nl + getExpr e + " end"
    | ExprType (TypeId tId, t) -> "type " + tId + " = " + getDecl t
    //| ExprNewType (TypeId tId, t) -> "datatype " + tId + " = " + getDecl t
    | ExprInclude (ModuleId m) -> "load " + m
    | ExprSequence es -> 
        let n = Seq.length es
        es |> Seq.mapi (fun i e -> 
            getExpr e + 
            (if i < n-1 then 
                match e with 
                |ExprBind _ 
                |ExprRecBind _ -> " in " 
                |ExprType _ -> ";;"
                |_ -> "; " 
            else ""))
        |> delim nl //|> surround "(" ")"
    
