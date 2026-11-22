-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_residue_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:31.516649+00:00
-- url     : https://prove2.me/submissions/601fc9b3-0659-46f6-ba8d-389403d6d7af

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_residue_expansion

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (T : ℕ) :
    integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) =
      ∑ a : Fin m, g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) := by
  classical
  unfold integerAverage
  simp_rw [residue_expansion hm g]
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc]
end LongGapsBetweenPrimes
