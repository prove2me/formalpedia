-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_cutoff_small_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:25:32.976442+00:00
-- url     : https://prove2.me/submissions/0fdc6dac-bc3a-4833-941c-f15b8a30258d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_zero_near_origin
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (r : ℝ → ℝ)
    (hsmall : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2)
    (e : ℝ) (he : 0 < e) :
    ∃ m : ℕ, ∀ z : ℝ,
      |r z - r z * min 1 (max 0 (|z| * ((m:ℝ)+1)-1))| ≤ e*z^2 := by
  obtain ⟨δ,hδ,hb⟩ := hsmall e he
  obtain ⟨m,hm⟩ := exists_nat_gt (2/δ)
  refine ⟨m,fun z => ?_⟩
  let c : ℝ := min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
  have hc := (Kyprianou.Ch04.ito43_cutoff_zero_near_origin m).2.1 z
  change |r z-r z*c| ≤ e*z^2
  by_cases hz : |z| ≤ δ
  · have hc0 : 0 ≤ 1-c := sub_nonneg.mpr hc.2
    have hc1 : 1-c ≤ 1 := by linarith [hc.1]
    rw [show r z-r z*c = r z*(1-c) by ring,abs_mul,abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)).trans (by simpa using hb z hz)
  · have hm' : 2 < (m:ℝ)*δ := (div_lt_iff₀ hδ).mp hm
    have hh : 2 ≤ |z| * ((m:ℝ)+1) := by
      have h := mul_le_mul_of_nonneg_right (le_of_not_ge hz) (show 0 ≤ (m:ℝ) by positivity)
      nlinarith [abs_nonneg z]
    have hc' : c = 1 := by
      dsimp [c]
      exact min_eq_left ((show 1 ≤ |z| * ((m:ℝ)+1)-1 by linarith).trans (le_max_right _ _))
    rw [hc',mul_one,sub_self,abs_zero]
    positivity
