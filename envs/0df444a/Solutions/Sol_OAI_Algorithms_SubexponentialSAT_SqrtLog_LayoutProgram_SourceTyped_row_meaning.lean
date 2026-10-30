-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:58.298885+00:00
-- url     : https://prove2.me/submissions/15edbee7-e13b-4afe-96e0-9e3f5cfa16ec

import Mathlib
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S100
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_sourceCode_decode

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

variable [DecidableEq V]

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

namespace PolynomialCode

theorem denote_sum (ps : List (PolynomialCode E)) :
    (sum ps).denote = (ps.map denote).sum := by
  induction ps with
  | nil => simp [sum, denote]
  | cons p ps ih => simp [sum, denote, ← ih, sum]

theorem denote_product (ps : List (PolynomialCode E)) :
    (product ps).denote = (ps.map denote).prod := by
  induction ps with
  | nil => simp [product, denote]
  | cons p ps ih => simp [product, denote, ← ih, product]

end PolynomialCode

section FiniteCode

variable {Q : ℕ} {node : Fin Q → E}

theorem basisCode_denote (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) :
    (basisCode u s i).denote = basis u s i := by
  have hs : Finset.univ.filter (fun a : Fin Q => a ≠ i ∧ a ∈ s) = s.erase i := by
    ext a
    simp
  simp [basisCode, PolynomialCode.denote, PolynomialCode.denote_product,
    List.map_ofFn, Fin.prod_ofFn, basis, basisDivisor, ← Finset.prod_filter,
    sub_eq_add_neg, apply_ite, hs]

theorem correctionCode_denote (u : NodeUnits node) (s : Finset (Fin Q)) (d : Fin Q → E) :
    (correctionCode u s d).denote = correctionPolynomial u s d := by
  simp [correctionCode, PolynomialCode.denote_sum, List.map_ofFn, Fin.sum_ofFn,
    PolynomialCode.denote, basisCode_denote, correctionPolynomial,
    apply_ite]

variable [Fintype V] [DecidableEq C]

theorem mismatchRowCode_denote (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (u : NodeUnits node) (d : V → Fin Q → E) (y : V) :
    (mismatchRowCode v head σ R u d y).denote = mismatchRowPath v head σ R u d y := by
  by_cases hy : (mismatchPositions head σ y).card ≤ R <;>
    simp [mismatchRowCode, PolynomialCode.denote, correctionCode_denote,
      mismatchRowPath, rowPath, mismatchCorrection, columnCorrection, hy]

end FiniteCode

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRepresentedRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Polynomial rows generated from represented field operations

The producer uses code words, finite expression constructors, and the supplied
arithmetic callbacks. It never extracts coefficients from an abstract field
value. Inverse constants are computed by finite-field powering. The canonical
coefficient lift is applied only after compiling the source polynomial.
-/

namespace SubexponentialSAT.SubexpRepresentedRows

open SubexpSymbolicCost SubexpRowInterpolation SubexpTaylorExecution

variable {C E : Type*} {Q : ℕ}

section Structural

variable [CommRing E] (ops : RepresentedRing C E)

private theorem map_sumCode (ps : List (PolynomialCode C)) :
    mapCode ops.decode (sumCode ops.zeroRun.1 ps) =
      PolynomialCode.sum (ps.map (mapCode ops.decode)) := by
  induction ps with
  | nil => simp [sumCode, PolynomialCode.sum, mapCode, ops.zero_correct]
  | cons p ps ih => simpa only [sumCode, List.foldr_cons, mapCode, List.map_cons,
      PolynomialCode.sum] using congrArg (PolynomialCode.add (mapCode ops.decode p)) ih

private theorem map_productCode (ps : List (PolynomialCode C)) :
    mapCode ops.decode (productCode ops.oneRun.1 ps) =
      PolynomialCode.product (ps.map (mapCode ops.decode)) := by
  induction ps with
  | nil => simp [productCode, PolynomialCode.product, mapCode, ops.one_correct]
  | cons p ps ih => simpa only [productCode, List.foldr_cons, mapCode, List.map_cons,
      PolynomialCode.product] using congrArg (PolynomialCode.mul (mapCode ops.decode p)) ih

variable (cache : NodeCache C Q) {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)

include hnode hinv hdiff in
theorem map_basis (s : Finset (Fin Q)) (i : Fin Q) :
    mapCode ops.decode (basis ops.program cache s i) = basisCode units s i := by
  simp only [basis, basisCode, mapCode, hinv, map_productCode, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  split_ifs <;> simp [mapCode, ops.neg_correct, hnode, hdiff, ops.one_correct]

include hnode hinv hdiff in
theorem map_correction (s : Finset (Fin Q)) (d : Fin Q → C) :
    mapCode ops.decode (correction ops.program cache s d) =
      correctionCode units s (fun i => ops.decode (d i)) := by
  simp only [correction, RepresentedRing.program, map_sumCode, correctionCode, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  split_ifs
  · change (PolynomialCode.constant (ops.decode (d i))).mul
      (mapCode ops.decode (basis ops.program cache s i)) = _
    rw [map_basis ops cache units hnode hinv hdiff]
  · simp only [mapCode, ops.zero_correct]

include hnode hinv hdiff in
theorem map_row {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) :
    mapCode ops.decode (row ops.program cache v head σ R d y) =
      mismatchRowCode v head σ R units (fun y i => ops.decode (d y i)) y := by
  simp only [row, mapCode, mismatchRowCode, RepresentedRing.program]
  congr 1
  · split_ifs with h
    · subst y; simp [ops.one_correct]
    · simp [h, ops.zero_correct]
  · by_cases hy : y ∈ correctionColumns head σ R
    · simp only [ite_eq_left hy]
      exact map_correction ops cache units hnode hinv hdiff _ _
    · simp only [ite_eq_right hy, mapCode, ops.zero_correct]

end Structural

end SubexponentialSAT.SubexpRepresentedRows

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

private theorem sum_selected {R : Type*} [AddCommMonoid R]
    (s : Finset (Fin Q)) (f : Fin Q → R) : ((selected s).map f).sum = ∑ i ∈ s, f i := by
  rw [← List.sum_toFinset f (selected_nodup s), selected_toFinset]

private theorem prod_selected {R : Type*} [CommMonoid R]
    (s : Finset (Fin Q)) (f : Fin Q → R) : ((selected s).map f).prod = ∏ i ∈ s, f i := by
  rw [← List.prod_toFinset f (selected_nodup s), selected_toFinset]

section Correctness

variable [CommRing E] (ops : RepresentedRing C E) (cache : NodeCache C Q)
variable {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)

private theorem rowExpression_eval (r : Row (Polynomial E)) :
    (rowExpression Polynomial.X r).eval = r.delta +
      (r.terms.map (fun t => (termExpression Polynomial.X t).eval)).sum := by
  change r.delta + (Algorithm.Expr.sum (r.terms.map (termExpression Polynomial.X))).eval = _
  simp only [Algorithm.Expr.eval_sum, List.map_map, Function.comp_def]

include hnode hdiff in
private theorem factorData_eval (i j : Fin Q) :
    (factorExpression Polynomial.X
      (mapFactor (fun x => Polynomial.C (ops.decode x)) (factorData ops.program cache i j))).eval =
      basisDivisor units i j := by
  simp [factorExpression, mapFactor, factorData, Algorithm.Expr.eval, ops.neg_correct, hnode, hdiff, basisDivisor, sub_eq_add_neg]

include hnode hinv hdiff in
private theorem termData_eval (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q) :
    (termExpression Polynomial.X
      (mapTerm (fun x => Polynomial.C (ops.decode x)) (termData ops.program cache s d i))).eval =
      Polynomial.C (ops.decode (d i)) * SubexpRowInterpolation.basis units s i := by
  simp only [termExpression, mapTerm, termData, Algorithm.Expr.eval, Algorithm.Expr.eval_product,
    List.map_map, Function.comp_def, hinv]
  simp_rw [factorData_eval ops cache units hnode hdiff]
  rw [prod_selected]
  rfl

include hnode hinv hdiff in
theorem rowData_eval {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) :
    (rowExpression Polynomial.X
      (mapRow (fun x => Polynomial.C (ops.decode x))
        (rowData ops.program cache v head σ R d y))).eval =
      (SubexpTaylorExecution.mapCode ops.decode
        (SubexpRepresentedRows.row ops.program cache v head σ R d y)).denote := by
  rw [SubexpRepresentedRows.map_row ops cache units hnode hinv hdiff,
    mismatchRowCode_denote]
  have hdelta : ops.decode (if v = y then ops.oneRun.1 else ops.zeroRun.1) =
      (Pi.single v (1 : E) : V → E) y := by
    by_cases h : v = y
    · subst y; simp [ops.one_correct]
    · simp [h, ops.zero_correct]
  have hdelta_program : ops.decode
      (if v = y then ops.program.oneRun.1 else ops.program.zeroRun.1) =
      (Pi.single v (1 : E) : V → E) y := hdelta
  rw [rowExpression_eval]
  by_cases hy : y ∈ correctionColumns head σ R
  · simp only [mapRow, rowData, ite_eq_left hy,
      List.map_map, Function.comp_def, hdelta_program]
    simp_rw [termData_eval ops cache units hnode hinv hdiff]
    rw [sum_selected]
    simp only [mismatchRowPath, rowPath, mismatchCorrection, columnCorrection,
      ite_eq_left hy, correctionPolynomial]
  · simp [ mapRow, rowData, hy, hdelta, mismatchRowPath, rowPath, mismatchCorrection,
      columnCorrection ]

end Correctness

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

theorem mapRow_comp (f : C → A) (g : A → B) (row : Row C) :
    mapRow g (mapRow f row) = mapRow (g ∘ f) row := by
  cases row
  simp [mapRow, _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapTerm, _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapFactor, List.map_map, Function.comp_def]

variable (ops : RingProgram C) (cache : NodeCache C Q) (encode : C → List Bool)
variable (t : UniversalRowLoop.Tables)

/-- Individual cache words may use any valid representation of their
scalars. No equality of the raw representatives is needed. -/
theorem map_factors_eq (decode : List Bool → A) (decodeC : C → A)
    (s : Finset (Fin Q)) (i : Fin Q)
    (hdifference : ∀ j : Fin Q, decode ((t.differences.getD i.val []).getD j.val []) =
      decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1)) :
    (UniversalRowFactorLoop.factors (t.differences.getD i.val []) t.negatives
      i.val (positions s)).map (_root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapFactor decode) =
      (UniversalRowSource.selected (s.erase i)).map
        (fun j => _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapFactor decodeC (factorData ops cache i j)) := by
  unfold UniversalRowFactorLoop.factors
  rw [positions_filter, positions]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j _
  simp only [_root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapFactor, UniversalRowFactorLoop.factor, factorData, hdifference, hnegative]

theorem map_term_eq (decode : List Bool → A) (decodeC : C → A)
    (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q)
    (hvalue : decode (t.values.getD i.val []) = decodeC (d i))
    (hinverse : decode (t.inverses.getD i.val []) = decodeC (cache.inverse i))
    (hdifference : ∀ j : Fin Q, decode ((t.differences.getD i.val []).getD j.val []) =
      decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1)) :
    _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapTerm decode (UniversalRowLoop.term t (positions s) i.val) =
      _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapTerm decodeC (termData ops cache s d i) := by
  simp only [UniversalRowLoop.term, UniversalRowTermProgram.term, _root_.OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource.mapTerm, termData,
    List.map_map]
  rw [hvalue, hinverse,
    map_factors_eq ops cache t decode decodeC s i hdifference hnegative]
  rfl

theorem map_row_eq (decode : List Bool → A) (decodeC : C → A)
    {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, decode (t.values.getD i.val []) = decodeC (d y i))
    (hinverse : ∀ i : Fin Q, decode (t.inverses.getD i.val []) = decodeC (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      decode ((t.differences.getD i.val []).getD j.val []) = decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1))
    (hdelta : decode delta = decodeC (if v = y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length = R) :
    mapRow decode
      (UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit) =
      mapRow decodeC (rowData ops cache v head σ R d y) := by
  simp only [UniversalRowDataProgram.row, mapRow, rowData, positions_length, hlimit, hdelta]
  by_cases h : (mismatchPositions head σ y).card ≤ R
  · have hy : y ∈ correctionColumns head σ R := (mem_correctionColumns head σ R y).mpr h
    simp only [ite_eq_left h, ite_eq_left hy, positions, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    exact map_term_eq ops cache t decode decodeC _ (d y) i (hvalue i) (hinverse i)
      (hdifference i) hnegative
  · have hy : y ∉ correctionColumns head σ R := by
      simpa only [mem_correctionColumns] using h
    simp [h, hy]

/-- A scalar-by-scalar decoder refinement suffices for the full polynomial.
The concrete input words need not equal a separately generated canonical
representative of the same field element. -/
theorem row_eval_of_decode [CommRing E] (source : RepresentedRing C E)
    {node : Fin Q → E} (units : NodeUnits node)
    (hnode : ∀ i, source.decode (cache.node i) = node i)
    (hinv : ∀ i, source.decode (cache.inverse i) = units.nodeInverse i)
    (hdiff : ∀ i j, source.decode (cache.difference i j) = units.differenceInverse i j)
    (decode : List Bool → E)
    {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, decode (t.values.getD i.val []) = source.decode (d y i))
    (hinverse : ∀ i : Fin Q,
      decode (t.inverses.getD i.val []) = source.decode (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      decode ((t.differences.getD i.val []).getD j.val []) =
        source.decode (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      source.decode ((source.negRun (cache.node j)).1))
    (hdelta : decode delta =
      source.decode (if v = y then source.oneRun.1 else source.zeroRun.1))
    (hlimit : limit.length = R) :
    (rowExpression Polynomial.X (mapRow (fun bits => Polynomial.C (decode bits))
      (UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit))).eval =
      (SubexpTaylorExecution.mapCode source.decode
        (SubexpRepresentedRows.row source.program cache v head σ R d y)).denote := by
  have hr := map_row_eq source.program cache t decode source.decode v head σ R d y
    delta limit hvalue hinverse hdifference hnegative hdelta hlimit
  have hc := congrArg (mapRow (Polynomial.C : E → Polynomial E)) hr
  simp only [mapRow_comp, Function.comp_def] at hc
  rw [hc]
  exact rowData_eval source cache units hnode hinv hdiff v head σ R d y

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical Lagrange row-source emitter instantiated with integer-derived
ring scalars. Its inputs are scalar arrays, not a preassembled polynomial or
instruction stream. Upstream proofs must supply the scalar arrays and their
individual decode laws; the concrete emitter itself is fully traced. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution
open SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open LayoutScaledMatrices

variable {C O : Type*} [CommRing O] {r Q Δ : ℕ}
variable (ops : RepresentedRing C O) (cache : NodeCache C Q)
variable (integerWord : ℤ → C) (hinteger : ∀ z, ops.decode (integerWord z) = (z : O))
variable (denominator : Oˣ) (inverseDenominator : C)
variable (hinverse : ops.decode inverseDenominator = (↑(denominator⁻¹) : O))
variable {node : Fin Q → O} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hnodeInv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)
variable (decode : List Bool → O) (tables : UniversalRowLoop.Tables)
variable (A R : ℕ) (u y : UniversalType r Q Δ) (i : Fin Δ)
variable (delta limit : List Bool)
variable (hvalue : ∀ t : Fin Q, decode (tables.values.getD t.val []) =
  ops.decode (sourceValue ops.program integerWord inverseDenominator A R u i y t))
variable (hinverses : ∀ t : Fin Q, decode (tables.inverses.getD t.val []) =
  ops.decode (cache.inverse t))
variable (hdifferences : ∀ t s : Fin Q,
  decode ((tables.differences.getD t.val []).getD s.val []) =
  ops.decode (cache.difference t s))
variable (hnegatives : ∀ t : Fin Q, decode (tables.negatives.getD t.val []) =
  ops.decode ((ops.negRun (cache.node t)).1))
variable (hdelta : decode delta = ops.decode (if u = y then ops.oneRun.1 else ops.zeroRun.1))
variable (hlimit : limit.length = R)

include hinteger hinverse hnode hnodeInv hdiff hvalue hinverses hdifferences hnegatives hdelta hlimit in
theorem tableSource_eq :
    (UniversalRowProgram.rowExpression Polynomial.X
      (UniversalRowSource.mapRow (fun bits => Polynomial.C (decode bits))
        (UniversalRowDataProgram.row tables
          (UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y))
          delta limit))).eval =
      sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  rw [UniversalRowTableSource.row_eval_of_decode cache tables ops units
    hnode hnodeInv hdiff decode u (fun v => v.head) (u.slot i) R
    (sourceValue ops.program integerWord inverseDenominator A R u i) y delta limit
    hvalue hinverses hdifferences hnegatives hdelta hlimit]
  exact sourceCode_decode ops integerWord hinteger denominator inverseDenominator hinverse
    cache units hnode hnodeInv hdiff A R u i y

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

theorem wordDecode_encode [Nonempty C] (encode : C → List Bool) (hi : Function.Injective encode)
    (decode : C → O) (c : C) : wordDecode encode decode (encode c)=decode c := by
  rw [wordDecode,Function.leftInverse_invFun hi c]

variable [CommRing O] (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

include hvalues hinverse hnegative hdifference hinteger hinvDenom hnode hnodeInverse hdiffInverse in
/-- Arbitrary valid native coefficient representations give the exact source
row over O, with full degree at most R. -/
theorem row_meaning_oai [Nonempty C] {r : ℕ} (hi : Function.Injective encode)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
    (hlimit : limit.length=R)
    (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
    let typed := row values inverse negative difference (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
    (rowExpression Polynomial.X (UniversalRowSource.mapRow (fun c => Polynomial.C (ops.decode c)) typed)).eval=
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y := by
  intro typed
  let decode := wordDecode encode ops.decode
  have hdecode : ∀ c,decode (encode c)=ops.decode c := wordDecode_encode encode hi ops.decode
  have h := LayoutProgram.tableSource_eq ops cache integerWord hinteger denom invDenom hinvDenom
    units hnode hnodeInverse hdiffInverse decode tables A R u y (0:Fin 1) (encode delta) limit
    (fun i => by rw [hvalues,hdecode,hv])
    (fun i => by rw [hinverse,hdecode,hiv])
    (fun i j => by rw [hdifference,hdecode,hdv])
    (fun i => by rw [hnegative,hdecode,hnv])
    (by rw [hdecode,hdelta]) hlimit
  rw [row_eq encode tables values inverse negative difference hvalues hinverse hnegative hdifference,
    hlimit,UniversalRowTableSource.mapRow_comp] at h
  have hfun : (fun bits => Polynomial.C (decode bits)) ∘ encode=
      fun c => Polynomial.C (ops.decode c) := by funext c; simp [hdecode]
  rw [hfun] at h
  exact h

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning_oai.{u_1, u_2}
