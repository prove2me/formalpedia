-- Prove2me | solution 1 for LongGapsBetweenPrimes.average_localBasis_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:36.753796+00:00
-- url     : https://prove2.me/submissions/e0948562-f660-431f-b017-95013b621aaf

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_average_residueFactor
import Theorems.Thm_LongGapsBetweenPrimes_average_residueFactor_sq
import Theorems.Thm_LongGapsBetweenPrimes_average_residueFactor_mul

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (hroot : Function.Injective root) (i j : Option (Fin k)) :
    Finset.expect Finset.univ (fun t => localBasis root i t * localBasis root j t) =
      localKernel p i j := by
  classical
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp)
  have : NeZero p := ⟨by omega⟩
  cases i with
  | none =>
      cases j <;>
        simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp,
          Finset.expect_const Finset.univ_nonempty]
  | some a =>
      cases j with
      | none =>
          simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp]
      | some b =>
          simp_rw [localBasis, mul_mul_mul_comm (Real.sqrt _) _ (Real.sqrt _) _]
          rw [← Finset.mul_expect, ← pow_two, Real.sq_sqrt hpR.le]
          by_cases hab : a = b
          · subst b
            simp only [localKernel, ← pow_two, average_residueFactor_sq hp]
            exact mul_one_div_cancel (ne_of_gt hpR)
          · rw [average_residueFactor_mul hp _ _ (hroot.ne hab)]
            simp only [localKernel, if_neg hab]
            field_simp
end LongGapsBetweenPrimes
