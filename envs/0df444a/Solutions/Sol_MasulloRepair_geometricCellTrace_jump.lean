-- Prove2me | solution 1 for MasulloRepair.geometricCellTrace_jump
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T20:45:51.014186+00:00
-- url     : https://prove2.me/submissions/4ba4483b-61cc-4660-8f96-7db1071a565d

import Definitions.Def_MasulloRepair_geometricCellTrace

open scoped BigOperators

lemma geo_hsum (r : ℂ) (c : ℕ → ℂ) (j : ℕ) :
    (∑ k ∈ Finset.range j, (r ^ 2) ^ (j - k) * c (k + 1)) =
      r ^ 2 * ∑ k ∈ Finset.range j, (r ^ 2) ^ (j - 1 - k) * c (k + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < j := Finset.mem_range.mp hk
  have hnat : j - k = (j - 1 - k) + 1 := by omega
  rw [hnat, pow_succ]
  ring

theorem solution (r : ℂ) (c : ℕ → ℂ) (j : ℕ) :
    MasulloRepair.geometricCellTrace r c (j + 1) - r ^ 2 * MasulloRepair.geometricCellTrace r c j =
      (1 - r ^ 2) * c (j + 1) := by
  unfold MasulloRepair.geometricCellTrace
  rw [show j + 1 - 1 = j by omega]
  rw [Finset.sum_range_succ]
  rw [geo_hsum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  ring
