-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:04:53.878525+00:00
-- url     : https://prove2.me/submissions/3e7dee71-582a-453d-ad24-e76ccd342de2

import Mathlib
import Definitions.Def_OAIQ081S075

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive Pascal-prefix cache for the original parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open Matrix SubexponentialSAT.BinomialInterpolation

theorem H_succ_succ (A m : ℕ) :
    H (A + 1) (m + 1) = H A (m + 1) + 2 * H (A + 1) m := by rw [H]

theorem shift_mulVec (R : ℕ) (v : Fin R → ℤ) (j : Fin R) :
    (shift R *ᵥ v) j = if h : j.val + 1 < R then v ⟨j.val + 1, h⟩ else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, shift]
  split_ifs with h
  · let k : Fin R := ⟨j.val + 1, h⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b hb hbk
      have hne : j.val + 1 ≠ b.val := by
        intro he
        apply hbk
        exact Fin.ext he.symm
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    have hne : j.val + 1 ≠ b.val := by omega
    simp [hne]

theorem binomial_succ (A R : ℕ) :
    SubexponentialSAT.BinomialMatrix.B ℤ (A + 1) R =
      SubexponentialSAT.BinomialMatrix.B ℤ A R * (1 + shift R) := by
  classical
  rw [Matrix.mul_add, Matrix.mul_one]
  ext d j
  simp only [Matrix.add_apply, SubexponentialSAT.BinomialMatrix.B_apply, Matrix.mul_apply, shift]
  by_cases hj : j.val = 0
  · simp [hj]
  · have hjpos : 0 < j.val := by omega
    let k : Fin R := ⟨j.val - 1, by omega⟩
    rw [Finset.sum_eq_single k]
    · have hjk : k.val + 1 = j.val := by dsimp [k]; omega
      simp only [hjk, ite_true, if_true, mul_one]
      have hp := Nat.choose_succ_succ (A + d.val) k.val
      rw [show A + 1 + d.val = (A + d.val) + 1 by omega, ← hjk, hp]
      push_cast
      ring
    · intro b hb hbk
      have hne : b.val + 1 ≠ j.val := by
        intro he
        apply hbk
        apply Fin.ext
        dsimp [k]
        omega
      simp [hne]
    · simp

theorem parity_step_vector (A R : ℕ) :
    parityCoefficients (K := ℤ) (A + 1) R +
      shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R =
        -parityCoefficients (K := ℤ) A R := by
  let B := SubexponentialSAT.BinomialMatrix.B ℤ A R
  let target : Fin R → ℤ := fun d => (-1 : ℤ) ^ (A + 1 + d.val)
  have hleft : B *ᵥ (parityCoefficients (K := ℤ) (A + 1) R +
      shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R) = target := by
    have hf : (1 + shift R) *ᵥ parityCoefficients (K := ℤ) (A + 1) R =
        parityCoefficients (K := ℤ) (A + 1) R +
          shift R *ᵥ parityCoefficients (K := ℤ) (A + 1) R := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
    rw [← hf, Matrix.mulVec_mulVec]
    change (SubexponentialSAT.BinomialMatrix.B ℤ A R * (1 + shift R)) *ᵥ _ = _
    rw [← binomial_succ]
    exact mulVec_coefficients _ (isUnit_det_binomial (A + 1) R) _
  have hright : B *ᵥ (-parityCoefficients (K := ℤ) A R) = target := by
    rw [Matrix.mulVec_neg]
    change -(SubexponentialSAT.BinomialMatrix.B ℤ A R *ᵥ
      coefficients (SubexponentialSAT.BinomialMatrix.B ℤ A R) (fun d => (-1 : ℤ) ^ (A + d.val))) = _
    rw [mulVec_coefficients _ (isUnit_det_binomial A R)]
    funext d
    simp only [Pi.neg_apply, target]
    rw [show A + 1 + d.val = (A + d.val) + 1 by omega, pow_succ]
    ring
  exact (coefficients_unique B (isUnit_det_binomial A R) target _ hleft).trans
    (coefficients_unique B (isUnit_det_binomial A R) target _ hright).symm

theorem parity_step (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) (A + 1) R j +
      (if h : j.val + 1 < R then parityCoefficients (K := ℤ) (A + 1) R
        ⟨j.val + 1, h⟩ else 0) = -parityCoefficients (K := ℤ) A R j := by
  have h := congrFun (parity_step_vector A R) j
  simpa only [Pi.add_apply, Pi.neg_apply, shift_mulVec] using h

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrenceFormula
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact identification of the positive cache with the original coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation

theorem parity_zero (R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) 0 R j = (-2 : ℤ) ^ j.val := by
  rw [LayoutCoefficientBounds.parity_upper_recurrence]
  have hz : (∑ k : Fin R, if j.val < k.val then
      (Nat.choose 0 (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) 0 R k
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    split_ifs with h
    · simp [Nat.choose_eq_zero_of_lt (show 0 < k.val - j.val by omega)]
    · rfl
  rw [hz]
  simp

/-- The unsigned cache gives the exact original integer interpolation vector. -/
theorem parity_eq_H (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      (-1 : ℤ) ^ (A + j.val) * 2 ^ j.val * (H A (R - 1 - j.val) : ℤ) := by
  induction A generalizing j with
  | zero =>
    rw [parity_zero]
    simp only [H_zero, Nat.cast_one, mul_one, zero_add]
    rw [← mul_pow]
    norm_num
  | succ A ih =>
    cases R with
    | zero => exact Fin.elim0 j
    | succ n =>
      induction j using Fin.reverseInduction with
      | last =>
        have hs := parity_step A (n + 1) (Fin.last n)
        simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero] at hs
        rw [ih] at hs
        simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, H_zero_right,
          Nat.cast_one, mul_one] at hs ⊢
        rw [show A + 1 + n = (A + n) + 1 by omega, pow_succ]
        linear_combination hs
      | cast j hj =>
        have hs := parity_step A (n + 1) j.castSucc
        simp only [Fin.val_castSucc] at hs
        rw [dite_eq_left (show j.val + 1 < n + 1 by omega)] at hs
        change parityCoefficients (K := ℤ) (A + 1) (n + 1) j.castSucc +
          parityCoefficients (K := ℤ) (A + 1) (n + 1) j.succ =
          -parityCoefficients (K := ℤ) A (n + 1) j.castSucc at hs
        rw [hj, ih] at hs
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel] at hs ⊢
        have hn : n - j.val = (n - (j.val + 1)) + 1 := by omega
        rw [hn, H_succ_succ]
        rw [← hn]
        push_cast
        rw [show A + 1 + j.val = (A + j.val) + 1 by omega, pow_succ]
        rw [show A + 1 + (j.val + 1) = (A + j.val) + 2 by omega,
          pow_add] at hs
        simp only [pow_succ] at hs
        norm_num at hs
        linear_combination hs

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open scoped BigOperators
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

theorem coefficientAt_H (A R j : ℕ) (hj : j < R) :
    LayoutCoefficientAlgorithm.coefficientAt A R j =
      (-1 : ℤ)^(A+j)*2^j*(H A (R-1-j) : ℤ) := by
  rw [LayoutCoefficientAlgorithm.coefficientAt_eq]
  simpa [SubexponentialSAT.BinomialInterpolation.extendCoefficients,hj] using parity_eq_H A R ⟨j,hj⟩

theorem factoredTerm_eq (A R d h k : ℕ) (hk : k < R-d) :
    factoredTerm A R d h k = (-1 : ℤ)^d *
      (LayoutCoefficientAlgorithm.coefficientAt A R (d+k) *
        2^(R-1-(d+k)) * (h.choose k : ℤ)) := by
  have hj : d+k < R := by omega
  have he : d+k+(R-1-(d+k)) = R-1 := by omega
  have hm : R-1-d-k = R-1-(d+k) := by omega
  have hs : (-1 : ℤ)^d * (-1)^(A+(d+k)) = (-1)^(A+k) := by
    rw [← pow_add, show d+(A+(d+k)) = (A+k)+2*d by omega,
      pow_add, pow_mul]
    norm_num
  have hp : (2 : ℤ)^(R-1) = 2^(d+k)*2^(R-1-(d+k)) := by rw [← pow_add,he]
  rw [coefficientAt_H A R (d+k) hj]
  unfold factoredTerm
  rw [hm]
  calc
    _ = ((-1 : ℤ)^d * (-1)^(A+(d+k))) *
        (H A (R-1-(d+k)) : ℤ) * (2^(d+k)*2^(R-1-(d+k))) * (h.choose k : ℤ) := by
      rw [hp,hs]
    _ = _ := by ring

theorem factoredEncodes_sum_oai (A R d h : ℕ) (xs : List Triple)
    (he : FactoredEncodes A R d h xs) :
    (xs.map termValue).sum = scalarSum A R d h := by
  have hl : List.ofFn (fun k : Fin xs.length => termValue (xs.get k)) =
      xs.map termValue := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (f := xs.get) (g := termValue)).symm
  calc
    _ = (List.ofFn (fun k : Fin xs.length => termValue (xs.get k))).sum := by rw [hl]
    _ = ∑ k : Fin xs.length, termValue (xs.get k) := List.sum_ofFn
    _ = ∑ k : Fin xs.length, factoredTerm A R d h k.val := by
      apply Finset.sum_congr rfl
      intro k _
      rcases he.2 k with ⟨hc,hp,hb⟩
      simp only [termValue,hc,hp,hb,factoredTerm]
    _ = ∑ k ∈ Finset.range xs.length, factoredTerm A R d h k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => factoredTerm A R d h k) xs.length
    _ = ∑ k ∈ Finset.range (R-d), (-1 : ℤ)^d *
        (LayoutCoefficientAlgorithm.coefficientAt A R (d+k)*
          2^(R-1-(d+k))*(h.choose k : ℤ)) := by
      rw [he.1]
      apply Finset.sum_congr rfl
      intro k hk
      exact factoredTerm_eq A R d h k (Finset.mem_range.mp hk)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramSemantics.lean

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/

/-! One consumer-facing contract for native triple preparation. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum_oai
