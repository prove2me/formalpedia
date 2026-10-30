-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:50:12.056629+00:00
-- url     : https://prove2.me/submissions/8fd16644-9149-4e27-8bc1-e3710705ed06

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S142
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_scalarProgram_runsIn_total
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_prepareProgram_factored_runsIn

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem numeratorPorts_injective : Function.Injective numeratorPorts := by decide

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

theorem numeratorPreparePorts_injective : Function.Injective numeratorPreparePorts :=
  Fin.castAdd_injective _ _
theorem numeratorScalarRegisters_injective : Function.Injective numeratorScalarRegisters :=
  Fin.castAdd_injective _ _
theorem numeratorScalarPorts_injective : Function.Injective numeratorScalarPorts := by decide

private theorem numeratorPrepare_embed (c : Cache) (regs r : Fin 9 → Bool)
    (counter parity queue : List Bool) :
    embedState id numeratorPreparePorts (numeratorState c regs counter parity [] ([],[]))
      (cacheState c r [] [] [] [] queue []) = numeratorState c r [] [] queue ([],[]) := by
  apply embedState_eq_of_ports id numeratorPreparePorts _ _ _
    Function.injective_id numeratorPreparePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> simp [numeratorState,cacheState,numeratorPreparePorts]
  · intro i hi
    have hv : 20 ≤ i.val := by
      by_contra h
      exact hi ⟨⟨i.val,by omega⟩,Fin.ext rfl⟩
    fin_cases i <;> simp_all [numeratorState]

private theorem numeratorPrepare_project (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) :
    projectState id numeratorPreparePorts (numeratorState c regs counter parity [] ([],[])) =
      cacheState c regs counter [] [] [] [] parity := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [numeratorState,numeratorPreparePorts]

private theorem numeratorFold_project (c : Cache) (regs : Fin 9 → Bool) (queue : List Bool) :
    projectState numeratorScalarRegisters numeratorScalarPorts
      (numeratorState c regs [] [] queue ([],[])) =
      state (regs ∘ numeratorScalarRegisters) ([],[]) ([],[]) ([],[]) queue := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [numeratorState,numeratorScalarPorts]

private theorem numeratorFold_embed (c : Cache) (regs : Fin 9 → Bool)
    (r : Fin 8 → Bool) (queue : List Bool) (result : WordPair) :
    ∃ rout, embedState numeratorScalarRegisters numeratorScalarPorts
      (numeratorState c regs [] [] queue ([],[])) (state r result ([],[]) ([],[]) []) =
      numeratorState c rout [] [] [] result := by
  let frame := numeratorState c regs [] [] queue ([],[])
  let e := embedState numeratorScalarRegisters numeratorScalarPorts frame
    (state r result ([],[]) ([],[]) [])
  refine ⟨e.regs,?_⟩
  apply embedState_eq_of_ports numeratorScalarRegisters numeratorScalarPorts _ _ _
    numeratorScalarRegisters_injective numeratorScalarPorts_injective
  · intro i
    exact embedState_register numeratorScalarRegisters numeratorScalarPorts frame
      (state r result ([],[]) ([],[]) []) numeratorScalarRegisters_injective i
  · intro i hi
    exact embedState_register_frame numeratorScalarRegisters numeratorScalarPorts frame
      (state r result ([],[]) ([],[]) []) i hi
  · intro i; fin_cases i <;> simp [numeratorState,state,numeratorScalarPorts]
  · intro i hi
    have hrange : ∀ j : Fin 25, 7 ≤ j.val → j ∈ Set.range numeratorScalarPorts := by decide
    have hv : i.val < 7 := by
      by_contra h
      exact hi (hrange i (by omega))
    fin_cases i <;> simp_all [numeratorState]

/-- Cached numerator endpoint. The cache-value and total invariants are input
representation predicates discharged by the concrete cache builders. -/
theorem numeratorProgram_runsIn (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) (A R d h Q : ℕ)
    (hc : counter.length = R-d) (ha : parity.length = A)
    (hu : c.Uniform) (hf : c.Fits (R-d))
    (hv : c.Values A R h) (hm : c.Totals A R h)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
    ∃ r result,
      RunsIn numeratorProgram
        (numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
          numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1)
        ((numeratorState c regs counter parity [] ([],[])).withPC
          (some numeratorProgram.entry))
        ((numeratorState c r [] [] [] result).withPC none) ∧
      pairValue result = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power) := by
  obtain ⟨rp,xs,⟨tp,htp,hprep⟩,hx,_,hb,hvalue,hmass⟩ :=
    prepareProgram_factored_runsIn c regs counter parity A R d h hc ha hu hf hv hm
  have hp := eval_call_from_state prepareProgram id numeratorPreparePorts
    (numeratorState c regs counter parity [] ([],[])) Function.injective_id
    numeratorPreparePorts_injective (by
      simpa only [numeratorPrepare_project] using hprep)
  rw [numeratorPrepare_embed] at hp
  obtain ⟨rf,result,⟨tf,htf,hfold⟩,hval,htotal,hlen⟩ :=
    scalarProgram_runsIn_total xs (rp ∘ numeratorScalarRegisters) ([],[]) 0
      (2*c.width.length+pairLength c.power) (by rfl) hb
  have hs := eval_call_from_state scalarProgram numeratorScalarRegisters numeratorScalarPorts
    (numeratorState c rp [] [] (pairEncoding (tripleWords xs)) ([],[]))
    numeratorScalarRegisters_injective numeratorScalarPorts_injective (by
      simpa only [numeratorFold_project] using hfold)
  obtain ⟨r,he⟩ := numeratorFold_embed c rp rf (pairEncoding (tripleWords xs)) result
  rw [he] at hs
  refine ⟨r,result,⟨tp+tf+1,?_,compiled_halt_trace (hp.seq hs) 7 23⟩,?_,?_,?_⟩
  · have hlenx : xs.length = R-d := hx.1
    simp only [hlenx,Nat.zero_add] at htf
    change tp ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power) at htp
    change tf ≤ numeratorFoldCost (R-d) c.width.length (pairLength c.power) at htf
    omega
  · simpa only [show pairValue ([],[]) = 0 from rfl,zero_add,hvalue] using hval
  · have hcMass : ∀ j < R,
        (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs ≤ (4*Q)^R := by
      intro j _
      rw [LayoutCoefficientAlgorithm.coefficientAt_eq]
      exact LayoutCoefficientBounds.natAbs_extend_parityCoefficients_le A R Q j hAQ hQ
    have hbound := LayoutProgram.scalarMass_le R d h Q hQ hhQ _ hcMass
    rw [← hmass] at hbound
    have ht : wordTotal result = (xs.map termTotal).sum := by
      simpa only [show wordTotal ([],[]) = 0 from rfl,zero_add] using htotal
    exact ht.trans_le hbound
  · simpa only [Nat.zero_add,hx.1] using hlen

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

private theorem numerator_ports_cover (j : Fin 40)
    (h : j.val ≤ 4 ∨ j=9 ∨ j=11 ∨ (12 ≤ j.val ∧ j.val ≤ 27) ∨ j=37 ∨ j=38) :
    j∈Set.range numeratorPorts := by
  have hc : ∀ k : Fin 40, k.val ≤ 4 ∨ k=9 ∨ k=11 ∨ (12 ≤ k.val ∧ k.val ≤ 27) ∨ k=37 ∨ k=38 →
      k∈Set.range numeratorPorts := by decide
  exact hc j h

private theorem numerator_project (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
    (n ac : List Bool)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power) :
    projectState id numeratorPorts
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[])) =
      numeratorState cache regs n ac [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [state,numeratorPorts,hp,hn,hw,hpower]

private theorem numerator_embed (c : Saved) (cache : Cache) (regs rf : Fin 9 → Bool)
    (n ac : List Bool) (result : WordPair)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power) :
    embedState id numeratorPorts
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
      (numeratorState cache rf [] [] [] result) =
      state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result := by
  apply embedState_eq_of_ports id numeratorPorts _ _ _ Function.injective_id numeratorPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> simp [state,numeratorPorts,numeratorState,hp,hn,hw,hpower]
  · intro i hi
    have hnone := fun hj => hi (numerator_ports_cover i hj)
    fin_cases i <;> first | exact (hnone (by decide)).elim | simp [state]

theorem numerator_eval_oai (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
    (n ac : List Bool) (A R d h Q : ℕ)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power)
    (hc : n.length=R-d) (ha : ac.length=A)
    (hu : cache.Uniform) (hf : cache.Fits (R-d)) (hv : cache.Values A R h) (hm : cache.Totals A R h)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
    ∃ t ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
      numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1,
    ∃ rf result, Eval numerator t
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
      (state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power) := by
  obtain ⟨rf,result,⟨t,ht,he⟩,hval,htotal,hlen⟩ :=
    numeratorProgram_runsIn cache regs n ac A R d h Q hc ha hu hf hv hm hAQ hQ hhQ
  have hh := eval_call_from_state numeratorProgram id numeratorPorts
    (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
    Function.injective_id numeratorPorts_injective
    (by simpa only [numerator_project c cache regs n ac hp hn hw hpower] using he)
  rw [numerator_embed c cache regs rf n ac result hp hn hw hpower] at hh
  refine ⟨t,?_,rf,result,hh,hval,htotal,?_⟩
  · simpa only [hw,hpower] using ht
  · simpa only [hw,hpower] using hlen

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval_oai
