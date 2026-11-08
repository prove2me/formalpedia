-- Prove2me | solution 1 for NestedLogitNBR.nestRevenue_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:58:11.694414+00:00
-- url     : https://prove2.me/submissions/767dedb6-b920-4265-9c92-07ee047638fc

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_nestRevenue

open NestedLogitNBR in
theorem solution {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hord : Antitone (r i)) (k : Fin n)
    (hq : 0 < prefWeight v i (nbr k.val)) :
    nestRevenue r v i (nbr (k.val + 1)) ≤ nestRevenue r v i (nbr k.val) := by
  have hset : (nbr (k.val + 1) : Finset (Fin n)) = insert k (nbr k.val) := by
    ext j
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hnot : k ∉ (nbr k.val : Finset (Fin n)) := by
    simp [nbr]
  have hA : r i k * (∑ j ∈ (nbr k.val : Finset (Fin n)), v i j) ≤
      ∑ j ∈ (nbr k.val : Finset (Fin n)), r i j * v i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k := by
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Fin.le_def.mpr hj.le
    exact mul_le_mul_of_nonneg_right (hord hjk) (hv j)
  unfold nestRevenue prefWeight at *
  rw [hset, Finset.sum_insert hnot, Finset.sum_insert hnot]
  have hvk := hv k
  have hW : 0 < v i k + ∑ j ∈ (nbr k.val : Finset (Fin n)), v i j := by linarith
  rw [div_le_div_iff₀ hW hq]
  nlinarith [mul_nonneg hvk (sub_nonneg.mpr hA)]
