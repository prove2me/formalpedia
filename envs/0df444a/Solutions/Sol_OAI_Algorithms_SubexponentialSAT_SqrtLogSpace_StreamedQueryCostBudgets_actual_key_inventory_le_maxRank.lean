-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:27:25.248815+00:00
-- url     : https://prove2.me/submissions/b49d3fac-5034-4fef-a947-d66ae89cadec

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S114
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatures_card_integer_representative_le_rank

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
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

theorem triangular_sum_bound (R M : ℕ) (b : Fin R → ℕ)
    (hb : ∀ j, b j ≤ M + ∑ k : Fin R, if j.val < k.val then b k else 0) :
    (∑ j, b j) + M ≤ M * 2 ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
    have htail : ∀ j : Fin R, b j.succ ≤
        M + ∑ k : Fin R, if j.val < k.val then b k.succ else 0 := by
      intro j
      simpa [Fin.sum_univ_succ] using hb j.succ
    have hrest := ih (fun j => b j.succ) htail
    have hzero : b 0 ≤ M + ∑ k : Fin R, b k.succ := by
      simpa [Fin.sum_univ_succ] using hb 0
    rw [Fin.sum_univ_succ, pow_succ]
    nlinarith

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

theorem natAbs_parity_recurrence (A R : ℕ) (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j).natAbs ≤
      2 ^ j.val + ∑ k : Fin R, if j.val < k.val then
        A.choose (k.val - j.val) * (parityCoefficients (K := ℤ) A R k).natAbs
        else 0 := by
  rw [parity_upper_recurrence A R j]
  calc
    _ ≤ ((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val).natAbs +
        (∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0).natAbs := Int.natAbs_sub_le _ _
    _ ≤ _ := by
      have h := Int.natAbs_sum_le (Finset.univ : Finset (Fin R))
        (fun k => if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k else 0)
      have htwo : (2 : ℤ).natAbs = 2 := by norm_num
      simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
        Int.natAbs_natCast, htwo, one_pow, one_mul, apply_ite Int.natAbs,
        Int.natAbs_zero] using
        Nat.add_le_add_left h (((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val).natAbs)

/-- A coarse uniform bound suffices for O(R log Q) coefficient bit length. -/
theorem natAbs_parityCoefficients_le (A R Q : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q)
    (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j).natAbs ≤ (4 * Q) ^ R := by
  let b : Fin R → ℕ := fun k => Q ^ k.val *
    (parityCoefficients (K := ℤ) A R k).natAbs
  let M := Q ^ R * 2 ^ R
  have hb : ∀ i, b i ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
    intro i
    calc
      b i ≤ Q ^ i.val * (2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          A.choose (k.val - i.val) * (parityCoefficients (K := ℤ) A R k).natAbs
          else 0) := Nat.mul_le_mul_left _ (natAbs_parity_recurrence A R i)
      _ = Q ^ i.val * 2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          Q ^ i.val * (A.choose (k.val - i.val) *
            (parityCoefficients (K := ℤ) A R k).natAbs) else 0 := by
        rw [Nat.mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul (Nat.pow_le_pow_right hQ (Nat.le_of_lt i.isLt))
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt))
        · apply Finset.sum_le_sum
          intro k hk
          split_ifs with hik
          · have hc : A.choose (k.val - i.val) ≤ Q ^ (k.val - i.val) :=
              (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hAQ _)
            calc
              _ ≤ Q ^ i.val * (Q ^ (k.val - i.val) *
                  (parityCoefficients (K := ℤ) A R k).natAbs) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
              _ = b k := by
                rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hik)]
          · exact Nat.le_refl _
  have hs := triangular_sum_bound R M b hb
  have hj : b j ≤ ∑ i, b i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hsmall : (parityCoefficients (K := ℤ) A R j).natAbs ≤ b j := by
    dsimp [b]
    have hp : 1 ≤ Q ^ j.val := one_le_pow₀ hQ
    simpa using Nat.mul_le_mul_right (parityCoefficients (K := ℤ) A R j).natAbs hp
  calc
    _ ≤ M * 2 ^ R := hsmall.trans (hj.trans (le_trans (Nat.le_add_right _ _) hs))
    _ = (4 * Q) ^ R := by
      dsimp [M]
      rw [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring

theorem natAbs_extend_parityCoefficients_le (A R Q j : ℕ)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) :
    (extendCoefficients (parityCoefficients (K := ℤ) A R) j).natAbs ≤
      (4 * Q) ^ R := by
  by_cases hj : j < R
  · simpa [extendCoefficients, hj] using
      natAbs_parityCoefficients_le A R Q hAQ hQ ⟨j, hj⟩
  · simp [extendCoefficients, hj]

end SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramMagnitude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unsigned component-total budgets for the signed-pair implementation.
These bounds do not infer component size from the absolute signed difference.
The physical arithmetic refinement must prove its total obeys this recurrence. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open scoped BigOperators

theorem scalarMass_le_raw (R d h Q : ℕ) (hQ : 1 ≤ Q) (hh : h ≤ Q)
    (coefficientMass : ℕ → ℕ)
    (hc : ∀ j < R, coefficientMass j ≤ (4*Q)^R) :
    scalarMass R d h coefficientMass ≤ R * (4*Q)^R * 2^R * Q^R := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (R-d), (4*Q)^R * 2^R * Q^R := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : k < R-d := Finset.mem_range.mp hk
      have hj : d+k < R := by omega
      have hchoose : h.choose k ≤ Q^R :=
        ((Nat.choose_le_pow h k).trans (Nat.pow_le_pow_left hh k)).trans
          (Nat.pow_le_pow_right hQ (by omega))
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (hc _ hj) (Nat.pow_le_pow_right (by omega) (by omega))) hchoose
    _ ≤ R * (4*Q)^R * 2^R * Q^R := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      calc
        _ ≤ R * ((4*Q)^R * 2^R * Q^R) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = _ := by ring

theorem scalarMass_le (R d h Q : ℕ) (hQ : 1 ≤ Q) (hh : h ≤ Q)
    (coefficientMass : ℕ → ℕ)
    (hc : ∀ j < R, coefficientMass j ≤ (4*Q)^R) :
    scalarMass R d h coefficientMass ≤ (8*Q)^(2*R) := by
  have hR : R ≤ 2^R := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ R * (4*Q)^R * 2^R * Q^R := scalarMass_le_raw R d h Q hQ hh _ hc
    _ ≤ 2^R * (4*Q)^R * 2^R * Q^R := by gcongr
    _ = (16*Q^2)^R := by simp only [← mul_pow]; congr 1; ring
    _ ≤ (64*Q^2)^R := by gcongr; norm_num
    _ = (8*Q)^(2*R) := by rw [pow_mul]; congr 1; ring

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_LayoutSizes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Retained full integer rows have polynomial binary length. Bounds on these
mathematical records are separate from native every-prefix storage proofs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSizes

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutCoefficientAlgorithm

theorem natAbs_scalarSum_le (A R Q d h : ℕ) (hAQ : A ≤ Q)
    (hQ : 1 ≤ Q) (hh : h ≤ Q) :
    (scalarSum A R d h).natAbs ≤ (8 * Q) ^ (2 * R) := by
  have hc (j : ℕ) : (coefficientAt A R j).natAbs ≤ (4 * Q) ^ R := by
    rw [coefficientAt_eq]
    exact LayoutCoefficientBounds.natAbs_extend_parityCoefficients_le A R Q j hAQ hQ
  apply le_trans _ (LayoutProgram.scalarMass_le R d h Q hQ hh
    (fun j => (coefficientAt A R j).natAbs) (fun j _ => hc j))
  unfold scalarSum LayoutProgram.scalarMass
  rw [Int.natAbs_mul]
  simp only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
  convert Int.natAbs_sum_le (Finset.range (R - d))
    (fun k => coefficientAt A R (d + k) * 2 ^ (R - 1 - (d + k)) *
      (h.choose k : ℤ)) using 1
  all_goals try with_reducible_and_instances rfl
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem natAbs_scalarEntry_le {r Q Δ : ℕ} (i : Fin Δ) (t : Fin Q)
    (A R : ℕ) (hAQ : A ≤ Q) (u y : UniversalType r Q Δ) :
    (scalarEntry i t A R u y).natAbs ≤ (8 * Q) ^ (2 * R) := by
  unfold scalarEntry
  split_ifs
  · apply natAbs_scalarSum_le A R Q _ _ hAQ (by have := t.isLt; omega)
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin Q)
  · simp

theorem natAbs_localEntry_le {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j v : Fin D) :
    (LayoutProgram.localEntry P A R t j v).natAbs ≤
      LayoutProgram.constraintMassBound Q R := by
  have hQ : 1 ≤ Q := by have := t.isLt; omega
  have hone : 1 ≤ LayoutProgram.constraintMassBound Q R := by
    unfold LayoutProgram.constraintMassBound
    exact (one_le_pow₀ (show 1 ≤ 8 * Q by omega)).trans (Nat.le_add_right _ _)
  unfold LayoutProgram.localEntry
  split
  · split_ifs <;> simp_all
  · split
    · simp
    · split
      · calc
          _ ≤ _ := Int.natAbs_sub_le _ _
          _ ≤ 2 ^ (R - 1) + (8 * Q) ^ (2 * R) := by
            apply Nat.add_le_add
            · split <;> norm_num [Int.natAbs_pow]
            · exact natAbs_scalarEntry_le _ _ _ _ hAQ _ _
          _ = _ := by simp [LayoutProgram.constraintMassBound, Nat.add_comm]
      · simp

/-- The height grows with the actual owner fiber, preserving the bounded
incidence parameter needed for the attained-signature time estimate. -/
theorem natAbs_literalMatrix_le_fiber {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j : Fin D) (v : Fin n) :
    (LayoutProducedMatrix.literalMatrix P owner A R t j v).natAbs ≤
      (Finset.univ.filter (fun i => owner i = v)).card *
        LayoutProgram.constraintMassBound Q R := by
  unfold LayoutProducedMatrix.literalMatrix LayoutPullback.row
  calc
    _ ≤ ∑ i : Fin D, (if owner i = v then LayoutProgram.localEntry P A R t j i
        else 0).natAbs := Int.natAbs_sum_le _ _
    _ = ∑ i ∈ Finset.univ.filter (fun i => owner i = v),
        (LayoutProgram.localEntry P A R t j i).natAbs := by
      simp only [Finset.sum_filter, apply_ite Int.natAbs, Int.natAbs_zero]
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => owner i = v),
        LayoutProgram.constraintMassBound Q R := by
      apply Finset.sum_le_sum
      intro i _
      exact natAbs_localEntry_le P A R hAQ t j i
    _ = _ := by simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSizes
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section KeyEncoding

theorem card_representative_kernel {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    Nat.card (AttainedSignatures.Representative actual) =
      Nat.card (AttainedSignatures.Representative model) :=
  Nat.card_congr (representativeKernelEquiv actual model hkernel)

end KeyEncoding

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRankBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single proof-only rank parameter for finitely many nodes or queries.
The maximum is used only in the analysis of attained signatures; it does not
require a runtime row-basis computation or bound the number of stored rows. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

theorem totalRank_le_max {X G : Type*} [Fintype G]
    (nodes : Finset X) (rank : X → G → ℕ) {x : X} (hx : x ∈ nodes) :
    (∑ g, rank x g) ≤ maxTotalRank nodes rank := by
  change (∑ g, rank x g) ≤ nodes.sup (fun y => ∑ g, rank y g)
  exact Finset.le_sup (f := fun y => ∑ g, rank y g) hx

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyInventory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical endpoint for the actual attained bucket product. The semantic
identification of each produced matrix and table is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

theorem jointInventory_le_rankSum {G : Type*} [Fintype G]
    (base : ℕ) (count rank : G → ℕ) (h : ∀ g, count g ≤ base^rank g) :
    (∏ g, count g) ≤ base^(∑ g, rank g) := by
  calc
    _ ≤ ∏ g, base^rank g := Finset.prod_le_prod' (fun g _ => h g)
    _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ rank base

theorem inventory_le_maxTotalRank {X G : Type*} [Fintype G]
    (base K : ℕ) (nodes : Finset X) (rank : X → G → ℕ) {x : X}
    (hbase : 1 ≤ base) (hx : x∈nodes) (hK : K ≤ base^(∑ g,rank x g)) :
    K ≤ base^maxTotalRank nodes rank :=
  hK.trans (Nat.pow_le_pow_right hbase (totalRank_le_max nodes rank hx))

theorem jointInventory_le_maxTotalRank {X G : Type*} [Fintype G]
    (base : ℕ) (count : G → ℕ) (nodes : Finset X) (rank : X → G → ℕ) {x : X}
    (hbase : 1 ≤ base) (hx : x∈nodes) (h : ∀ g,count g ≤ base^rank x g) :
    (∏ g,count g) ≤ base^maxTotalRank nodes rank :=
  inventory_le_maxTotalRank base _ nodes rank hbase hx
    (jointInventory_le_rankSum base count (rank x) h)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryCostBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The new traversal charges only attained full integer signatures. Its
predecessor rescans and complete-tuple visitors are additive, and the pair
count is bounded by the square of the original ambient support count. These
numerical comparisons use fixed powers of the original explicit cost; they
do not assert a machine execution or supply an evaluator service. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal
open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets

noncomputable section
open Classical

/-- Actual owner-fiber multiplicity bounds every retained integer entry,
in the selected-ID order used by the native head loader. -/
theorem selected_integer_entry_le {r Q D n : ℕ}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R B : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (t : Fin Q) (js : List ℕ) (hjs : ∀ v ∈ js, v < n)
    (j : Fin D) (i : Fin js.length) :
    |LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i)| ≤
      (B * LayoutProgram.constraintMassBound Q R : ℕ) := by
  have hi : js.get i < n := hjs _ (List.get_mem ..)
  rw [LayoutProducedMatrix.literalNat, dite_eq_left j.isLt, dite_eq_left hi,
    ← Int.natCast_natAbs]
  exact_mod_cast (LayoutSizes.natAbs_literalMatrix_le_fiber
    packing owner A R hAQ t j ⟨js.get i,hi⟩).trans
      (Nat.mul_le_mul_right _ (hB ⟨js.get i,hi⟩))

/-- This is the original maximum of the actual selected matrix ranks.
It requires no bucket tables and never replaces that rank by the larger
canonical pullback rank. The key may be any faithful physical encoding. -/
theorem actual_key_inventory_le_maxRank_oai
    {r Q D n : ℕ} {κ : Fin r → Type*}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R B height : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hheight : B * LayoutProgram.constraintMassBound Q R ≤ height)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (t : Fin Q) (ht : t ∈ nodes)
    (key : (g : Fin r) → Fin (2 ^ (LeafHeadSetupProgram.selectedHeads n rows low
      (t.val*r+g.val)).length) → κ g)
    (hkernel : ∀ g x y, key g x = key g y ↔
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) x =
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) y) :
    (∏ g : Fin r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
      (2*n*height+1) ^ CostAssembly.maxTotalRank nodes
        (BucketProgram.ProducedRank.actualRank packing owner A R rows low) := by
  apply CostAssembly.jointInventory_le_maxTotalRank _ _ nodes _ (by omega) ht
  intro g
  let js := LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)
  have hj : ∀ v ∈ js, v < n := HeadIdentifierProgram.chosenIds_bound _ _
  have hn : js.length ≤ n := HeadIdentifierProgram.count_le _ _
  rw [← Nat.card_eq_fintype_card, card_representative_kernel (key g)
    (AttainedSignatures.integerKey (fun (j : Fin D) (i : Fin js.length) =>
      LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i))) (hkernel g)]
  have hc := AttainedSignatures.card_integer_representative_le_rank
    (fun (j : Fin D) (i : Fin js.length) =>
      LayoutProducedMatrix.literalNat packing owner A R t j.val (js.get i))
    (B * LayoutProgram.constraintMassBound Q R)
    (selected_integer_entry_le packing owner A R B hAQ hB t js hj)
  apply hc.trans
  apply Nat.pow_le_pow_left
  gcongr

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank_oai.{u_1}
