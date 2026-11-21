-- Prove2me | solution 1 for MasulloRH.critical_width_translated_global_gram_density
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:26:18.235848+00:00
-- url     : https://prove2.me/submissions/f22a1660-22d7-4ee1-94d0-ae8407393a95

import Mathlib
open Filter Topology
theorem solution :
    let w := fun x : ℝ => Real.exp |x| * (1 + x^2)^2
    (∀ x : ℝ, Tendsto (fun L : ℝ => w (x+L) / (Real.exp L * L^4))
      atTop (𝓝 (Real.exp x))) ∧
    (∀ x L : ℝ, 1 ≤ L → w (x+L) / (Real.exp L * L^4) ≤ 9 * w x) := by
  dsimp only
  constructor
  · intro x
    have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hr : Tendsto (fun L : ℝ => Real.exp x *
        ((L⁻¹)^2 + (x * L⁻¹ + 1)^2)^2) atTop (𝓝 (Real.exp x)) := by
      convert (tendsto_const_nhds (x := Real.exp x)).mul
        (((hi.pow 2).add (((tendsto_const_nhds (x := x)).mul hi |>.add
        (tendsto_const_nhds (x := (1:ℝ)))).pow 2)).pow 2) using 1 <;> simp
    apply hr.congr'
    filter_upwards [eventually_ge_atTop (max 1 (-x))] with L hL
    have hl : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
    have hx : 0 ≤ x+L := by linarith [(le_max_right (1:ℝ) (-x)).trans hL]
    rw [abs_of_nonneg hx, Real.exp_add]
    field_simp [ne_of_gt hl, Real.exp_ne_zero]
    <;> ring
  · intro x L hL
    have hl : 0 < L := by linarith
    have hl2 : 1 ≤ L^2 := by nlinarith [sq_nonneg (L-1)]
    have hxL : x^2 ≤ x^2 * L^2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hl2)]
    have hp : (1+(x+L)^2) ≤ 3*(1+x^2)*L^2 := by nlinarith [sq_nonneg (x-L),sq_nonneg x]
    have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(x+L)^2) hp 2
    have he : Real.exp |x+L| ≤ Real.exp |x| * Real.exp L := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simpa [abs_of_pos hl] using abs_add_le x L)
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ (Real.exp |x| * Real.exp L) * ((3*(1+x^2)*L^2)^2) :=
        mul_le_mul he hp2 (by positivity) (by positivity)
      _ = _ := by ring
