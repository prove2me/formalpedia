-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_summable_series_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:19:16.447634+00:00
-- url     : https://prove2.me/submissions/a0b513a2-4dbb-4170-89f1-f3e4346c8217

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {ι : Type} (f z : ι → ℝ)
    (hs : Summable (fun i => |f i|)) (h0 : ∀ i, z i = 0 → f i = 0) :
    Tendsto (fun m : ℕ => ∑' i, f i * min 1 (max 0 (|z i| * ((m:ℝ)+1)-1)))
      atTop (nhds (∑' i, f i)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro i
    by_cases hz : z i = 0
    · simp [h0 i hz]
    · have hp : 0 < |z i| := abs_pos.mpr hz
      obtain ⟨M,hM⟩ := exists_nat_gt (2/|z i|)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop M] with m hm
      have hm' : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have h := (div_lt_iff₀ hp).mp hM
      have h' : 1 ≤ |z i| * ((m:ℝ)+1)-1 := by
        nlinarith [mul_le_mul_of_nonneg_left hm' hp.le]
      rw [min_eq_left (h'.trans (le_max_right _ _)),mul_one]
  · filter_upwards [] with m i
    let c : ℝ := min 1 (max 0 (|z i| * ((m:ℝ)+1)-1))
    have hc : 0 ≤ c := le_min zero_le_one (le_max_left _ _)
    have hc' : c ≤ 1 := min_le_left _ _
    change ‖f i*c‖ ≤ |f i|
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hc]
    exact mul_le_of_le_one_right (abs_nonneg _) hc'
