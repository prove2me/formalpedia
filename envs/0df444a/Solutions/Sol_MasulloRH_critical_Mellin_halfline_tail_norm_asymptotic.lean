-- Prove2me | solution 1 for MasulloRH.critical_Mellin_halfline_tail_norm_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:24:22.455389+00:00
-- url     : https://prove2.me/submissions/4409f9f9-daeb-47b9-8804-8401d759e15f

import Mathlib
open Filter Topology MeasureTheory Set
theorem solution (a : ℝ) (ha : 0 < a) :
    let w : ℝ → ℝ := fun x => Real.exp |x| * (1+x^2)^2
    Tendsto (fun L : ℝ => ∫ y : ℝ in Ioi 0,
      Real.exp (a*L) * (1+L^2)^2 * Real.exp ((1-a)*(L+y)) / w (L+y))
      atTop (𝓝 a⁻¹) := by
  dsimp only
  let k (y L : ℝ) := ((1+L^2)/(1+(L+y)^2))^2
  have klim (y : ℝ) : Tendsto (fun L => k y L) atTop (𝓝 1) := by
    have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hc : Tendsto (fun L : ℝ => (1 + y*L⁻¹)^2) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add
        ((tendsto_const_nhds (x := y)).mul hi)).pow 2
    have hden : Tendsto (fun L : ℝ => (L⁻¹)^2+(1+y*L⁻¹)^2) atTop (𝓝 1) := by
      simpa using (hi.pow 2).add hc
    have hnum : Tendsto (fun L : ℝ => (L⁻¹)^2+1) atTop (𝓝 1) := by
      simpa using (hi.pow 2).add_const (1:ℝ)
    have ht : Tendsto (fun L : ℝ => (((L⁻¹)^2+1)/((L⁻¹)^2+(1+y*L⁻¹)^2))^2) atTop (𝓝 1) := by
      simpa using (hnum.div hden (by norm_num)).pow 2
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    dsimp [k]
    congr 1
    field_simp [ne_of_gt hL]
    <;> ring
  have hlim : Tendsto (fun L : ℝ => ∫ y : ℝ in Ioi 0, Real.exp (-a*y) * k y L)
      atTop (𝓝 (∫ y : ℝ in Ioi 0, Real.exp (-a*y))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => Real.exp (-a*y))
    · exact Eventually.of_forall (fun L => by
        have hc : Continuous (fun y : ℝ => Real.exp (-a*y) * k y L) := by dsimp [k]; fun_prop (disch := intro x; positivity)
        exact hc.aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := hy
      have hrs : 0 ≤ (1+L^2)/(1+(L+y)^2) := by positivity
      have hle : (1+L^2)/(1+(L+y)^2) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        nlinarith [mul_nonneg hL hy0.le, sq_nonneg y]
      have hk : k y L ≤ 1 := by dsimp [k]; nlinarith [mul_nonneg hrs (sub_nonneg.mpr hle)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [k]; positivity)]
      simpa using mul_le_mul_of_nonneg_left hk (Real.exp_pos (-a*y)).le
    · exact integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0
    · exact Eventually.of_forall (fun y => by simpa using (klim y).const_mul (Real.exp (-a*y)))
  have hi : (∫ y : ℝ in Ioi 0, Real.exp (-a*y)) = a⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_neg_of_pos ha)]
    simp
  rw [hi] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := hy
  dsimp [k]
  rw [abs_of_nonneg (show 0 ≤ L+y by linarith)]
  have he : Real.exp (a*L) * Real.exp ((1-a)*(L+y)) =
      Real.exp (-a*y) * Real.exp (L+y) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [div_pow]
  calc
    _ = (Real.exp (-a*y) * Real.exp (L+y)) * (1+L^2)^2 /
        (Real.exp (L+y)*(1+(L+y)^2)^2) := by
          field_simp [Real.exp_ne_zero]
          <;> ring
    _ = _ := by rw [← he]; ring
