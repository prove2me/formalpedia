-- Prove2me | solution 1 for MasulloRH.tapered_holomorphic_multiplier_boundary_jet_error
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:09:08.839777+00:00
-- url     : https://prove2.me/submissions/4dab7d63-d798-4831-a3ca-2e9af70a8462

import Mathlib
open MeasureTheory Filter Topology
private theorem hardy_poly_exp (u : ℝ) (hu : 0 ≤ u) :
    u * (1+u) * Real.exp (-u) ≤ 4 := by
  have hx := Real.add_one_le_exp (u / 2)
  have hy : u*(1+u) ≤ 4*(Real.exp (u/2)*Real.exp (u/2)) := by
    have hh := mul_self_le_mul_self (by linarith : 0 ≤ u / 2 + 1) hx
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos u)).2
  simpa only [← Real.exp_add, add_halves] using hy
theorem solution (z : ℝ → ℂ) (hz : Continuous z) (hr : ∀ t, 0 ≤ (z t).re)
    (G : ℝ → ℝ) (hG : Integrable G volume) :
    let a := fun (n : ℕ) => ((n:ℝ)+1)⁻¹
    let E := fun (n : ℕ) (t : ℝ) => Complex.exp (-(a n : ℂ)*z t)
    let v := fun (n : ℕ) (t : ℝ) => a n*(z t).re
    Tendsto (fun n => ∫ t : ℝ, (‖E n t-1‖^2 + (v n t*(1+v n t)*‖E n t‖)^2)*G t)
      atTop (𝓝 0) := by
  intro a E v
  have ha0 (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    dsimp only [a]
    apply tendsto_inv_atTop_zero.comp
    have hN : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    apply tendsto_atTop.2
    intro b
    filter_upwards [hN.eventually (eventually_ge_atTop b)] with n hn
    linarith
  have he (n : ℕ) (t : ℝ) : ‖E n t‖ = Real.exp (-(v n t)) := by
    simp [E, v, Complex.norm_exp, Complex.mul_re]
  have hm (n : ℕ) : Continuous (fun t => ‖E n t-1‖^2 + (v n t*(1+v n t)*‖E n t‖)^2) := by
    dsimp [E,v]; fun_prop
  have main : Tendsto (fun n => ∫ t : ℝ, (‖E n t-1‖^2 + (v n t*(1+v n t)*‖E n t‖)^2)*G t)
      atTop (𝓝 (∫ _t : ℝ, (0:ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun t => 20*‖G t‖)
    · exact fun n => (hm n).aestronglyMeasurable.mul hG.aestronglyMeasurable
    · exact hG.norm.const_mul 20
    · intro n
      apply Eventually.of_forall
      intro t
      have hv : 0 ≤ v n t := mul_nonneg (ha0 n) (hr t)
      have hle : ‖E n t‖ ≤ 1 := by rw [he]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
      have hs : ‖E n t - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
      have hh := hardy_poly_exp (v n t) hv
      rw [← he n t] at hh
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hpos : 0 ≤ v n t*(1+v n t)*‖E n t‖ := by positivity
      nlinarith [sq_nonneg (2-‖E n t-1‖), mul_nonneg (sub_nonneg.mpr hs) (by positivity : 0 ≤ 2+‖E n t-1‖), mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 4+v n t*(1+v n t)*‖E n t‖ by linarith)]
    · apply Eventually.of_forall
      intro t
      have hz' : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0) := by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp ha
      have hE : Tendsto (fun n => E n t) atTop (𝓝 1) := by
        simpa [E, Function.comp_def] using (Complex.continuous_exp.tendsto _).comp (hz'.neg.mul_const (z t))
      have hv : Tendsto (fun n => v n t) atTop (𝓝 0) := by simpa [v] using ha.mul_const (z t).re
      simpa using ((((hE.sub_const (1:ℂ)).norm.pow 2).add (((hv.mul (tendsto_const_nhds.add hv)).mul hE.norm).pow 2)).mul_const (G t))
  simpa using main
