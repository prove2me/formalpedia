-- Prove2me | solution 1 for MasulloRH.critical_width_square_root_cutoff_borderline_schedule
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T07:08:58.015696+00:00
-- url     : https://prove2.me/submissions/9a038ad2-64d1-4cca-a903-ac3e839d3393

import Mathlib
open Filter Topology
theorem solution :
    let L : ℝ → ℝ := fun n => n * Real.exp n
    let d : ℝ → ℝ := fun n => 2*n
    let X : ℝ → ℝ := fun n => Real.exp (L n)
    let cutoff : ℝ → ℝ := fun n => Real.exp (L n - d n)
    Tendsto (fun n => X n * (Real.log (Real.log (X n)) / Real.log (X n))^2 / cutoff n)
      atTop (𝓝 1) ∧
    Tendsto (fun n => Real.exp (-(d n)) * (1+(L n)^2)/(1+(d n)^2))
      atTop (𝓝 (1/4 : ℝ)) := by
  dsimp only
  constructor
  · have hlog : Tendsto (fun n : ℝ => Real.log n / n) atTop (𝓝 0) := by
      simpa using (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
    have hs : Tendsto (fun n : ℝ => (Real.log n / n + 1)^2) atTop (𝓝 1) := by
      simpa using (hlog.add (tendsto_const_nhds (x := (1:ℝ)))).pow 2
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with n hn
    simp only [Real.log_exp, Real.log_mul hn.ne' (Real.exp_ne_zero n), Real.exp_sub,
      show 2*n = n+n by ring, Real.exp_add]
    field_simp [Real.exp_ne_zero,hn.ne'] <;> ring
  · have hi : Tendsto (fun n : ℝ => n⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have he : Tendsto (fun n : ℝ => (Real.exp n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop
    have hs : Tendsto (fun n : ℝ => (((Real.exp n)⁻¹*n⁻¹)^2+1) / ((n⁻¹)^2+4))
        atTop (𝓝 (1/4:ℝ)) := by
      convert (((he.mul hi).pow 2).add (tendsto_const_nhds (x := (1:ℝ)))).div
        ((hi.pow 2).add (tendsto_const_nhds (x := (4:ℝ)))) (by norm_num) using 1 <;> norm_num <;> rfl
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with n hn
    rw [Real.exp_neg, show 2*n = n+n by ring, Real.exp_add]
    field_simp [Real.exp_ne_zero,hn.ne',show (1+(n+n)^2) ≠ 0 by positivity,
      show (1 + 4*n^2) ≠ 0 by positivity] <;> ring
