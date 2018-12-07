(* ::Package:: *)

(*** TensorKazas 2.0 ***)


(** Expressions, acceptable for tensor names and indexes **)


tNamePattern = _Symbol | _Symbol@___?AtomQ;


(** Service functions **)


SetAttributes[toString, HoldAll];
toString@args___ := 
	Function[arg, ToString[Unevaluated@arg, StandardForm], HoldAll] /@ 
		Unevaluated@{args};

(* Number of tensor indexes (tensor rank). Supports all types of indexes. *)
SetAttributes[iLength, HoldAll];
iLength@i___ := Length@Unevaluated@{i};


(* Raise message if a bad tensor expression was input. *)
SetAttributes[mes, HoldRest];
mes[check_, mes_, args___] := (
		If[!check, Message[mes, Sequence @@ toString@args]];
		check
	);
tensor::arr="Tensor `` is not an array.";
tensor::def="Tensor `` was not defined.";
tensor::npt="Name of a tensor `` is not proper.";
tensor::prp="Tensor `1` has indexes duplicated more than 2 times: `2`.";

(* Find out whether tensor x with rank of iLength@i was defined previously.
Supports all types of tensors and their indexes. *)
SetAttributes[tensorExistsQ, HoldAll];
tensorExistsQ[Subscript[x_, i___]] := mes[Head@tensor[x, iLength@i] =!= tensor, tensor::def, Subscript[x, i]];

(* Find out whether tensor indexes are not duplicated more than 2 times each.
Supports all types of indexes. *)
SetAttributes[properTensorQ, HoldAll];
properTensorQ[Subscript[x_, i___]] := 
	With[{gathered = Tally@toString@i}, 
		With[{check = TrueQ[And @@ Thread[gathered[[All, 2]] <= 2]]}, 
			If[check,
				check, 
				With[{wrong = StringRiffle[Select[gathered, #[[2]] > 2 &][[All, 1]], ", "]}, 
					mes[check, 
						tensor::prp, 
						Subscript[x, i],
						wrong
					]]]]];

SetAttributes[arrayQ, HoldAll];
arrayQ[x_] := mes[ArrayQ@x, tensor::arr, x];

SetAttributes[tNameMatchQ, HoldAll];
tNameMatchQ[Subscript[x_, i___]] := mes[MatchQ[x, tNamePattern], tensor::npt, Subscript[x, i]];
tNameMatchQ[x:Except@Subscript[_, ___]] := mes[MatchQ[x, tNamePattern], tensor::npt, x];


SetAttributes[iDuplicateFreeQ, HoldAll];
iDuplicateFreeQ[Subscript[x_, i___]] := !DuplicateFreeQ@Unevaluated@{i};

SetAttributes[iMatchQ, HoldAll];
iMatchQ[Subscript[x_, i___]] := MatchQ[Unevaluated@{i}, {tNamePattern...}];


(** "tensor" symbol contains data of corresponding indexed expressions **)


SetAttributes[Subscript, HoldAll];
SetAttributes[tensor, HoldFirst];

(* Define tensor onto previously defined array x. *)
HoldPattern@tensor[x_?tNameMatchQ] /; arrayQ@x :=
	tensor[x, ArrayDepth@x] = x;
(* Define tensor onto clean expression x with dimensions m. *)
HoldPattern@createTensor[x_?tNameMatchQ, {m__Integer}] :=
	tensor[x, Length@{m}] = Array[Subscript[x, ##] &, {m}];

(* Definition of commonly used symbols. *)
tensor[\[Epsilon], n_Integer] := LeviCivitaTensor[n];
tensor[\[Delta]@m_Integer, n_Integer] := Array[KroneckerDelta, ConstantArray[m, n]];


(** Tensors contraction in indexed appearance **)


(* Special number for defining new tensors during evaluation.
For example,  when first operation yields its result,  res[1] tensor will be defined,  then res[2],  etc. *)
Once[resultNumber = 0];

HoldPattern@Subscript[(x_?tNameMatchQ), i___] /;
		iMatchQ[Subscript[x, i]] && tensorExistsQ[Subscript[x, i]] && iDuplicateFreeQ[Subscript[x, i]] && properTensorQ[Subscript[x, i]] :=
	With[{
			pos=Select[Values@PositionIndex@Unevaluated@{i}, Length@#==2&],
			resultNumber=++resultNumber
		}, 
		
		tensor[res[resultNumber], iLength@i-2Length@pos]=
			TensorContract[tensor[x, iLength@i], pos];
			
		Unevaluated[Subscript[res[resultNumber], i]][[
			Prepend[1+Complement[Range@iLength@i, Flatten@pos], 1]
		]]
	];


(** Tensor production in indexed appearance **)


Once[
	ClearAttributes[Evaluate@TensorProduct, {Protected, ReadProtected}];
	HoldPattern[___ \[TensorProduct] 0 \[TensorProduct] ___] =.;
	SetAttributes[TensorProduct, {Protected, ReadProtected}];
];


HoldPattern[q0___ \[TensorProduct] Subscript[(x_?tNameMatchQ), i___] \[TensorProduct] Subscript[(y_?tNameMatchQ), j___] \[TensorProduct] q1___] /;
		tensorExistsQ[Subscript[x, i]] && tensorExistsQ[Subscript[y, j]] && properTensorQ[Subscript[x, i]] && properTensorQ[Subscript[y, j]] ^:=
	With[{resultNumber = ++resultNumber}, 
		tensor[res[resultNumber], iLength[i, j]] = tensor[x, iLength@i] \[TensorProduct] tensor[y, iLength@j];
		q0 \[TensorProduct] Subscript[res[resultNumber], i, j] \[TensorProduct] q1
	];


(** Evaluation of indexed tensor expression **)


tEval[expr_] := expr /. {
		HoldPattern@Subscript[(x_?tNameMatchQ), i:Except@_Integer...] :>
			tensor[x, iLength@i],
		
		HoldPattern@Subscript[(x_?tNameMatchQ), i___] :>
			tensor[x, iLength@i][[
				Sequence @@ Replace[Unevaluated@{i}, Except@_Integer -> All, {1}]
			]]
	};
