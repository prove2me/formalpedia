-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:44:05.50942+00:00
-- url     : https://prove2.me/submissions/a0d7f6f1-5c28-463f-b4e2-cf8c46baa77b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceTyped_source_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceExpression_typed_row_contract

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

theorem serializeCode_append {R : Type*} (encode : R → Word)
    (a b : List (Algorithm.Instr R)) :
    SubexpPostfixControl.serializeCode encode (a ++ b) =
      SubexpPostfixControl.serializeCode encode a ++
        SubexpPostfixControl.serializeCode encode b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [SubexpPostfixControl.serializeCode, ih, List.append_assoc]

theorem operators_succ (mul : Bool) (n : ℕ) :
    operators mul (n + 1) = operators mul n ++ operator mul := by
  simp [operators, List.replicate_succ', List.flatten_append]

theorem compile_sum {R : Type*} [Zero R] (encode : R → Word) (es : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (Algorithm.Expr.sum es).compile =
      (es.map (fun e => SubexpPostfixControl.serializeCode encode e.compile)).flatten ++
        pushWord (encode 0) ++ operators false es.length := by
  induction es with
  | nil => simp [Algorithm.Expr.sum, Algorithm.Expr.compile,
      SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, pushWord]
  | cons e es ih =>
      simp [Algorithm.Expr.sum, Algorithm.Expr.compile, serializeCode_append, ih,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        operators_succ, operator, List.append_assoc]

theorem compile_product {R : Type*} [One R] (encode : R → Word) (es : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (Algorithm.Expr.product es).compile =
      (es.map (fun e => SubexpPostfixControl.serializeCode encode e.compile)).flatten ++
        pushWord (encode 1) ++ operators true es.length := by
  induction es with
  | nil => simp [Algorithm.Expr.product, Algorithm.Expr.compile,
      SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, pushWord]
  | cons e es ih =>
      simp [Algorithm.Expr.product, Algorithm.Expr.compile, serializeCode_append, ih,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        operators_succ, operator, List.append_assoc]

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

@[simp] theorem operators_length (mul : Bool) (n : ℕ) :
    (operators mul n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [operators_succ, List.length_append, ih]; simp [operator]; omega

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

theorem factorCode_eq {R : Type*} (encode : R → Word) (x : R) (f : Factor R) :
    factorCode (encode x) (mapFactor encode f) =
      SubexpPostfixControl.serializeCode encode (factorExpression x f).compile := by
  simp [factorCode, mapFactor, factorExpression, Algorithm.Expr.compile, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr, pushWord, operator, List.append_assoc]

theorem productCode_eq {R : Type*} [One R] (encode : R → Word) (x : R) (fs : List (Factor R)) :
    productCode (encode 1) (encode x) (fs.map (mapFactor encode)) =
      SubexpPostfixControl.serializeCode encode
        (Algorithm.Expr.product (fs.map (factorExpression x))).compile := by
  rw [SubexpKernelControl.compile_product]
  simp [productCode, List.map_map, Function.comp_def, factorCode_eq]

theorem termCode_eq {R : Type*} [One R] (encode : R → Word) (x : R) (t : Term R) :
    termCode (encode 1) (encode x) (mapTerm encode t) =
      SubexpPostfixControl.serializeCode encode (termExpression x t).compile := by
  simp [termCode, mapTerm, termExpression, Algorithm.Expr.compile,
    SubexpKernelControl.serializeCode_append, productCode_eq,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    pushWord, operator, List.append_assoc]

theorem rowCode_eq {R : Type*} [Zero R] [One R] (encode : R → Word) (x : R) (r : Row R) :
    rowCode (encode 0) (encode 1) (encode x) (mapRow encode r) =
      SubexpPostfixControl.serializeCode encode (rowExpression x r).compile := by
  simp only [rowCode, mapRow, List.map_map, Function.comp_def, termCode_eq,
    rowExpression, Algorithm.Expr.compile, SubexpKernelControl.serializeCode_append,
    SubexpKernelControl.compile_sum]
  simp [SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    pushWord, operator, List.append_assoc]

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Filtered row records for the physical interpolation-code emitter

Inactive zero terms and unit factors are omitted from the emitted records.
This is proved as a polynomial identity, without identifying the two different
expression trees or assuming a desired evaluator result.
-/

namespace SubexponentialSAT.Subexp.UniversalRowSource

open scoped BigOperators
open SubexpSymbolicCost SubexpRowInterpolation SubexpRepresentedRows
open UniversalRowProgram

variable {C E : Type*} {Q : ℕ}

theorem selected_nodup (s : Finset (Fin Q)) : (selected s).Nodup :=
  (List.nodup_finRange Q).filter _

end SubexponentialSAT.Subexp.UniversalRowSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTableSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Indexed cache tables and the represented interpolation row

The physical producer reads natural-number indexed lists. This adapter
identifies those reads with the finite-indexed row specification, including
the mismatch filter and the cardinality guard. Its premises concern only
individual input cache entries, the delta word, and the limit's length.
-/

namespace SubexponentialSAT.Subexp.UniversalRowTableSource

open SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowSource
open UniversalRowProgram (Row rowExpression)

variable {C E A B : Type*} {Q : ℕ}

@[simp] theorem positions_length (s : Finset (Fin Q)) :
    (positions s).length = s.card := by
  rw [positions, List.length_map,
    ← List.toFinset_card_of_nodup (UniversalRowSource.selected_nodup s), selected_toFinset]

theorem positions_filter (s : Finset (Fin Q)) (i : Fin Q) :
    (positions s).filter (fun j => decide (j ≠ i.val)) = positions (s.erase i) := by
  unfold positions UniversalRowSource.selected
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro j _
  simp [ Fin.val_injective.eq_iff]

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem flat_eq_encode {d B : ℕ} (hB : 0 < B) (x : Code (Word B) d) :
    flat x = SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) (List.ofFn x) := by
  have aux (xs : List (Word B)) :
      (xs.map Subtype.val).flatten =
        SubexponentialSAT.StackEncoding.encodeDataStack (wordBlockCode B hB) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, List.flatten_cons,
        SubexponentialSAT.StackEncoding.encodeDataStack_cons, wordBlockCode] using congrArg (x.val ++ ·) ih
  change (List.ofFn (Subtype.val ∘ x)).flatten = _
  simpa only [List.map_ofFn] using aux (List.ofFn x)

theorem flat_injective {d B : ℕ} (hB : 0 < B) :
    Function.Injective (flat : Code (Word B) d → List Bool) := by
  intro x y h
  rw [flat_eq_encode hB, flat_eq_encode hB] at h
  exact List.ofFn_injective (SubexponentialSAT.StackEncoding.encodeDataStack_injective _ h)

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row-source emitter's bytes are exactly the input accepted by
the generic coefficient-array interpreter. Scalar literals are single cells;
the formal variable has the two-cell representation [zero, one]. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram

theorem sourceCode_eq {B d : ℕ} (ops : RingProgram (Coeff B d)) (r : Row (Coeff B d)) :
    rowCode (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1 ++ SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (mapRow SubexponentialSAT.SqrtLog.RingProgram.flat r) =
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode (sourceExpr ops r).compile := by
  let _ : Zero (List (Coeff B d)) := ⟨[ops.zeroRun.1]⟩
  let _ : One (List (Coeff B d)) := ⟨[ops.oneRun.1]⟩
  have hzero : (0 : List (Coeff B d)) = [ops.zeroRun.1] := rfl
  have hone : (1 : List (Coeff B d)) = [ops.oneRun.1] := rfl
  have h := rowCode_eq DensePolynomialProgram.encode [ops.zeroRun.1,ops.oneRun.1]
    (mapRow (fun c => [c]) r)
  have hmap : mapRow DensePolynomialProgram.encode (mapRow (fun c => [c]) r) =
      mapRow SubexponentialSAT.SqrtLog.RingProgram.flat r := by
    cases r
    simp [mapRow, mapTerm, mapFactor, DensePolynomialProgram.encode,
      List.map_map, Function.comp_def]
  rw [hmap] at h
  simpa [hzero, hone, sourceExpr, DensePolynomialProgram.encode] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed witnesses for the actual interpolation table reads. Cached negative
nodes and inverse differences need only have the right decoded value; no
canonical representation or equality with an arithmetic implementation is
assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowProgram SubexponentialSAT.Subexp.UniversalRowSource
open SubexponentialSAT.Subexp.UniversalRowTableSource SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation

variable {C O : Type*} {Q : ℕ}

variable (encode : C → List Bool) (tables : UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (hvalues : ∀ i, tables.values.getD i.val []=encode (values i))
    (hinverse : ∀ i, tables.inverses.getD i.val []=encode (inverse i))
    (hnegative : ∀ i, tables.negatives.getD i.val []=encode (negative i))
    (hdifference : ∀ i j, (tables.differences.getD i.val []).getD j.val []=encode (difference i j))

include hnegative hdifference in
theorem factors_eq (s : Finset (Fin Q)) (i : Fin Q) :
    UniversalRowFactorLoop.factors (tables.differences.getD i.val []) tables.negatives i.val (positions s)=
      (selected (s.erase i)).map (fun j => UniversalRowSource.mapFactor encode (factor negative difference i j)) := by
  unfold UniversalRowFactorLoop.factors
  rw [positions_filter,positions,List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_def,UniversalRowFactorLoop.factor,hdifference,hnegative,UniversalRowSource.mapFactor,factor]

include hvalues hinverse hnegative hdifference in
theorem term_eq (s : Finset (Fin Q)) (i : Fin Q) :
    UniversalRowLoop.term tables (positions s) i.val=
      UniversalRowSource.mapTerm encode (term values inverse negative difference s i) := by
  simp only [UniversalRowLoop.term,UniversalRowTermProgram.term,UniversalRowSource.mapTerm,term,List.map_map]
  rw [hvalues,hinverse,factors_eq encode tables negative difference hnegative hdifference]
  rfl

include hvalues hinverse hnegative hdifference in
/-- The actual raw row record is the encoding of a concrete typed row. -/
theorem row_eq (s : Finset (Fin Q)) (delta : C) (limit : List Bool) :
    UniversalRowDataProgram.row tables (positions s) (encode delta) limit=
      UniversalRowSource.mapRow encode (row values inverse negative difference s delta limit.length) := by
  simp only [UniversalRowDataProgram.row,row,UniversalRowSource.mapRow,positions_length]
  by_cases h : s.card ≤ limit.length
  · simp only [ite_eq_left h,positions,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    exact term_eq encode tables values inverse negative difference hvalues hinverse hnegative hdifference s i
  · simp [h]

variable [CommRing O] (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

/-- The generated bytes are precisely a typed postfix compiler output,
not merely a string with the desired denotation. -/
theorem code_witness {B d Q : ℕ}
    (ops : RingProgram (PolynomialExecutorProgram.Coeff B d))
    (tables : UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → PolynomialExecutorProgram.Coeff B d)
    (difference : Fin Q → Fin Q → PolynomialExecutorProgram.Coeff B d)
    (hvalues : ∀ i,tables.values.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (values i))
    (hinverse : ∀ i,tables.inverses.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (inverse i))
    (hnegative : ∀ i,tables.negatives.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (negative i))
    (hdifference : ∀ i j,(tables.differences.getD i.val []).getD j.val []=
      SubexponentialSAT.SqrtLog.RingProgram.flat (difference i j))
    (s : Finset (Fin Q)) (delta : PolynomialExecutorProgram.Coeff B d) (limit : List Bool) :
    rowCode (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1++SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (UniversalRowDataProgram.row tables (positions s) (SubexponentialSAT.SqrtLog.RingProgram.flat delta) limit)=
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode
      (PolynomialExecutorProgram.sourceExpr ops
        (row values inverse negative difference s delta limit.length)).compile := by
  rw [row_eq SubexponentialSAT.SqrtLog.RingProgram.flat tables values inverse negative difference
    hvalues hinverse hnegative hdifference]
  exact PolynomialExecutorProgram.sourceCode_eq ops _

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact table shapes and read validity for finite typed interpolation
caches. Flattening is a specification of the arrays produced natively. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

private theorem getD_ofFn {A : Type*} (f : Fin Q → A) (default : A) (i : Fin Q) :
    (List.ofFn f).getD i.val default=f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem tables_values (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).values.getD i.val []=encode (values i) :=
  getD_ofFn _ _ _

theorem tables_inverse (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).inverses.getD i.val []=encode (inverse i) :=
  getD_ofFn _ _ _

theorem tables_negative (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).negatives.getD i.val []=encode (negative i) :=
  getD_ofFn _ _ _

theorem tables_difference (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i j : Fin Q) :
    ((tables encode values inverse negative difference).differences.getD i.val []).getD j.val []=
      encode (difference i j) := by
  change ((List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i.val []).getD j.val []=_
  rw [getD_ofFn,getD_ofFn]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceWitness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete typed witness for one actual universal source word: compiler
bytes, full polynomial meaning, degree, and physical byte length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness
open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

variable {B d r Q : ℕ} {O : Type*} [CommRing O]

theorem universal_oai (ops : RepresentedRing (Coeff B d) O) (hB : 0 < B)
    (cache : NodeCache (Coeff B d) Q)
    (integerWord : ℤ → Coeff B d) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : Coeff B d) (hinv : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hni : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdi : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)
    (values inverse negative : Fin Q → Coeff B d) (difference : Fin Q → Fin Q → Coeff B d)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : Coeff B d) (limit : List Bool)
    (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hi : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hn : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdiff : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length=R)
    (width rowWidth : List Bool) (hw : width.length=d*B) (hrw : rowWidth.length=Q*width.length)
    (S : ℕ) (hQ : Q ≤ S) (hW : width.length ≤ S) (hRW : rowWidth.length ≤ S) (hR : R ≤ S) :
    Generated ops R (UniversalRowSourceBound.sourceLengthBound S)
      (LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y)
      (UniversalRowProgram.rowCode (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1)
        (RingProgram.flat ops.zeroRun.1++RingProgram.flat ops.oneRun.1)
        (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat values inverse negative difference)
          (UniversalRowTableSource.positions (mismatchPositions (fun v=>v.head) (u.slot 0) y))
          (RingProgram.flat delta) limit)) := by
  let : Nonempty (Coeff B d) := ⟨ops.zeroRun.1⟩
  let ts := SourceTyped.tables RingProgram.flat values inverse negative difference
  let s := mismatchPositions (fun v=>v.head) (u.slot 0) y
  let row := SourceTyped.row values inverse negative difference s delta R
  let e := sourceExpr ops.program row
  have hc := SourceTyped.code_witness ops.program ts values inverse negative difference
    (SourceTyped.tables_values _ _ _ _ _) (SourceTyped.tables_inverse _ _ _ _ _)
    (SourceTyped.tables_negative _ _ _ _ _) (SourceTyped.tables_difference _ _ _ _ _) s delta limit
  have hm := LayoutSourceExpression.typed_row_contract
    RingProgram.flat ts values inverse negative difference
    (SourceTyped.tables_values _ _ _ _ _) (SourceTyped.tables_inverse _ _ _ _ _)
    (SourceTyped.tables_negative _ _ _ _ _) (SourceTyped.tables_difference _ _ _ _ _)
    ops cache integerWord hinteger denom invDenom hinv units hnode hni hdi
    (RingProgram.flat_injective hB) A R u y delta limit hlimit hv hi hn hdiff hdelta
  have hlen (c : Coeff B d) : (RingProgram.flat c).length=width.length :=
    (RingProgram.flat_length c).trans hw.symm
  have hb := SourceTyped.source_bounds RingProgram.flat values inverse negative difference
    width rowWidth hlen hrw s (RingProgram.flat delta) limit
    (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1) S hQ hW hRW
    (by rw [hlen]; exact hW) (by rw [hlimit]; exact hR)
    (by rw [hlen]; exact hW) (by rw [hlen]; exact hW)
  refine ⟨e,?_,hm.1,hm.2.1,hb.2⟩
  simpa only [hlimit] using hc

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal_oai.{u_1}
