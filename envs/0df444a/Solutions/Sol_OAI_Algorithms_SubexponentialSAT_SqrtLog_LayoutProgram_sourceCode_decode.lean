-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:02:23.140302+00:00
-- url     : https://prove2.me/submissions/98d8ea99-b76b-43df-aaab-312e5523e0c1

import Mathlib
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S081
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm_scalarEntry_cast

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit exponential-in-R bounds for the existing integer parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open Matrix

theorem pascal_power_sum (R : ℕ) (d : Fin R) :
    (∑ j : Fin R, (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val) =
      (-1 : ℤ) ^ d.val := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) R]
  calc
    (∑ j ∈ Finset.range R, (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) =
        ∑ j ∈ Finset.range (d.val + 1), (d.val.choose j : ℤ) * (-2 : ℤ) ^ j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjd
      have h : d.val < j := by simpa using hjd
      simp [Nat.choose_eq_zero_of_lt h]
    _ = (-1 : ℤ) ^ d.val := by
      have h := add_pow (-2 : ℤ) 1 d.val
      norm_num only [one_pow, mul_one, show (-2 : ℤ) + 1 = -1 by norm_num] at h
      simpa [mul_comm] using h.symm

theorem upper_mulVec_parity (A R : ℕ) :
    (SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ parityCoefficients (K := ℤ) A R =
      fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val := by
  let c := parityCoefficients (K := ℤ) A R
  let g : Fin R → ℤ := fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val
  have hg : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ g =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    funext d
    simp only [Matrix.mulVec, dotProduct, SubexponentialSAT.BinomialMatrix.L_apply, g]
    calc
      (∑ j : Fin R, (d.val.choose j.val : ℤ) *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val)) =
          (-1 : ℤ) ^ A * ∑ j : Fin R,
            (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (-1 : ℤ) ^ (A + d.val) := by rw [pascal_power_sum, pow_add]
  have hc : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ
        ((SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ c) =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    rw [Matrix.mulVec_mulVec, ← SubexponentialSAT.BinomialMatrix.factorization]
    exact mulVec_coefficients _ (isUnit_det_binomial A R) _
  have hu : IsUnit (SubexponentialSAT.BinomialMatrix.L ℤ R).det := by simp
  have h1 := coefficients_unique _ hu _ _ hc
  have h2 := coefficients_unique _ hu _ _ hg
  exact h1.trans h2.symm

theorem parity_upper_recurrence (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val -
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
  have heq := congrFun (upper_mulVec_parity A R) j
  simp only [Matrix.mulVec, dotProduct] at heq
  have hsplit :
      (∑ k : Fin R, SubexponentialSAT.BinomialMatrix.U ℤ A R j k *
        parityCoefficients (K := ℤ) A R k) =
      parityCoefficients (K := ℤ) A R j +
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
    calc
      _ = ∑ k : Fin R,
          ((if k = j then parityCoefficients (K := ℤ) A R j else 0) +
          (if j.val < k.val then (A.choose (k.val - j.val) : ℤ) *
            parityCoefficients (K := ℤ) A R k else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k = j
        · subst k
          simp [SubexponentialSAT.BinomialMatrix.U]
        · by_cases hjk : j.val < k.val
          · simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, Nat.le_of_lt hjk]
          · have hn : ¬j.val ≤ k.val := by
              have hne : k.val ≠ j.val := fun he => h (Fin.ext he)
              omega
            simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, hn]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit] at heq
  omega

end SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable descending triangular solution for the original parity coefficients.
There are R coordinate updates, each scanning R potential upper entries.
No matrix inverse is executed. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

theorem solve_processed (A R n : ℕ) (hn : n ≤ R) (j : Fin R)
    (hj : R - n ≤ j.val) :
    solve A R n j = parityCoefficients (K := ℤ) A R j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    have hnr : n < R := by omega
    have hnle : n ≤ R := by omega
    let i : Fin R := ⟨R - 1 - n, by omega⟩
    change (if h : n < R then
      Function.update (solve A R n) (⟨R - 1 - n, by omega⟩ : Fin R)
        (target A (R - 1 - n) -
          upperTail A R (⟨R - 1 - n, by omega⟩ : Fin R) (solve A R n))
      else solve A R n) j = _
    rw [dite_eq_left hnr]
    by_cases hji : j = i
    · rw [hji]
      dsimp [i]
      simp only [Function.update, dite_true]
      rw [parity_upper_recurrence A R i]
      congr 1
      unfold upperTail
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with hik
      · rw [ih hnle k (by dsimp [i] at hik; omega)]
      · rfl
    · simp only [Function.update, dite_eq_right (by simpa only [i] using hji)]
      apply ih hnle j
      have hne : j.val ≠ R - 1 - n := fun he => hji (Fin.ext he)
      omega

theorem solve_eq (A R : ℕ) :
    solve A R R = parityCoefficients (K := ℤ) A R := by
  funext j
  exact solve_processed A R R (by omega) j (by omega)

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

theorem coefficientAt_eq (A R j : ℕ) :
    coefficientAt A R j = extendCoefficients (parityCoefficients (K := ℤ) A R) j := by
  simp [coefficientAt, extendCoefficients, solve_eq]

variable {r Q Δ : ℕ}

/-- Equality with the semantic integer numerator used in all rank and support proofs. -/
theorem scalarEntry_eq_entry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    scalarEntry i t A R u y = LayoutNumerator.entry i t A R u y := by
  have he := scalarEntry_cast i t A R u y
  have hc := LayoutNumerator.entry_cast ℚ (by norm_num) i t A R u y
  have hcoeff : (fun j => (coefficientAt A R j : ℚ)) =
      extendCoefficients (parityCoefficients (K := ℚ) A R) := by
    funext j
    rw [coefficientAt_eq, LayoutNumerator.extend_parityCoefficients_intCast]
  rw [hcoeff] at he
  exact_mod_cast he.trans hc.symm

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramRowCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The literal represented source-row circuit over the target ring. Integer
numerators are lifted directly, then multiplied by the supplied inverse of the
power-of-two denominator. There is no field section or inverse in the target
ring. The bit-program realizations of these measured scalar operations and
of the cache construction are separate obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution
open LayoutScaledMatrices

variable {C O : Type*} {r Q Δ : ℕ}

variable [CommRing O] (ops : RepresentedRing C O)
variable (integerWord : ℤ → C) (hinteger : ∀ z, ops.decode (integerWord z) = (z : O))
variable (denominator : Oˣ) (inverseDenominator : C)
variable (hinverse : ops.decode inverseDenominator = (↑(denominator⁻¹) : O))

include hinteger hinverse in
theorem sourceValue_decode (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) :
    ops.decode (sourceValue ops.program integerWord inverseDenominator A R u i y t) =
      SubexponentialSAT.SubexpAnnihilation.matrixPrescription (RingHom.id O)
        (fun t g j => unitScaled denominator (LayoutNumerator.family r Q Δ A R t g j))
        u i y t := by
  by_cases hu : u ∈ joint t (y.head t) i <;>
    by_cases hy : y ∈ joint t (y.head t) i
  all_goals
    simp [sourceValue, hu, hy, ops.zero_correct,
      ops.neg_correct, ops.mul_correct, hinteger, hinverse,
      SubexponentialSAT.SubexpAnnihilation.matrixPrescription,
      SubexponentialSAT.SubexpAnnihilation.zeroExtendMatrix, unitScaled,
      LayoutNumerator.family, LayoutNumerator.joint,
      LayoutCoefficientAlgorithm.scalarEntry_eq_entry]

include hinteger hinverse in
theorem sourceCode_decode_oai (cache : NodeCache C Q) {node : Fin Q → O}
    (units : NodeUnits node)
    (hnode : ∀ t, ops.decode (cache.node t) = node t)
    (hnodeInv : ∀ t, ops.decode (cache.inverse t) = units.nodeInverse t)
    (hdiff : ∀ t s, ops.decode (cache.difference t s) = units.differenceInverse t s)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) :
    (mapCode ops.decode (sourceCode ops.program cache integerWord inverseDenominator A R u i y)).denote =
      sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  unfold sourceCode
  rw [map_row ops cache units hnode hnodeInv hdiff, mismatchRowCode_denote]
  unfold sourceRow SubexponentialSAT.SubexpAnnihilation.rowForMatrices
  congr 2
  funext y t
  exact sourceValue_decode ops integerWord hinteger denominator inverseDenominator hinverse A R u i y t

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode_oai.{u_1, u_2}
