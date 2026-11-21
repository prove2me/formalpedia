-- Prove2me | solution 1 for MasulloGRH.sobolev_window_boundary_blowup
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:28:21.5851+00:00
-- url     : https://prove2.me/submissions/fd60feb1-c9a2-4c55-80fa-fed42845a26c

import Theorems.Thm_MasulloGRH_sobolev_window_jet_integrable_iff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution (m : ℕ) (s α : ℝ) (hs : 1 < s) (hα : 0 ≤ α)
    (horder : s ≤ 2 * (m : ℝ) + 1) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 α)) :
    Tendsto (fun n => ∫⁻ x : ℝ, ENNReal.ofReal
      (Real.exp (2 * b n * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)))) atTop (𝓝 ⊤) := by
  let F : ℝ → ℝ → ℝ := fun t x => Real.exp (2 * t * x - 2 * α * |x|) *
    (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))
  have hc (t : ℝ) : Continuous (F t) := by
    apply Continuous.mul (by fun_prop)
    apply Continuous.div (by fun_prop)
    · apply Continuous.rpow_const (by fun_prop)
      intro x
      exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))
    · intro x
      exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hpos (t x : ℝ) : 0 ≤ F t x := by
    dsimp [F]
    apply mul_nonneg (Real.exp_pos _).le
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  have hnot : ¬ Integrable (F α) := by
    rw [show F α = (fun x : ℝ => Real.exp (2 * α * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) from rfl,
      MasulloGRH.sobolev_window_jet_integrable_iff m s α α hs (by simp [abs_of_nonneg hα])]
    simp only [abs_of_nonneg hα, lt_self_iff_false, false_or]
    exact not_lt.mpr horder
  have hinfty : (∫⁻ x, ENNReal.ofReal (F α x)) = ⊤ := by
    by_contra h
    exact hnot ((lintegral_ofReal_ne_top_iff_integrable
      (hc α).aestronglyMeasurable (Filter.Eventually.of_forall (hpos α))).mp h)
  have hlim (x : ℝ) : Tendsto (fun n => ENNReal.ofReal (F (b n) x)) atTop
      (𝓝 (ENNReal.ofReal (F α x))) := by
    have ht : Continuous (fun t => F t x) := by dsimp [F]; fun_prop
    exact (ENNReal.continuous_ofReal.tendsto _).comp (ht.continuousAt.tendsto.comp hb)
  have hfatou := lintegral_liminf_le (μ := (volume : Measure ℝ)) (u := (atTop : Filter ℕ))
    (f := fun n x => ENNReal.ofReal (F (b n) x))
    (fun n => ENNReal.measurable_ofReal.comp (hc (b n)).measurable)
  have heq : (fun x => liminf (fun n => ENNReal.ofReal (F (b n) x)) atTop) =
      (fun x => ENNReal.ofReal (F α x)) := funext fun x => (hlim x).liminf_eq
  rw [heq, hinfty] at hfatou
  exact tendsto_of_le_liminf_of_limsup_le hfatou le_top
