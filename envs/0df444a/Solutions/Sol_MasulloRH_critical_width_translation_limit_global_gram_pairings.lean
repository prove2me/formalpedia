-- Prove2me | solution 1 for MasulloRH.critical_width_translation_limit_global_gram_pairings
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:30:14.943188+00:00
-- url     : https://prove2.me/submissions/4d83301f-bff1-4d04-b7b5-7c7aaa0ce774

import Theorems.Thm_MasulloRH_critical_width_translated_global_gram_density
import Mathlib
open MeasureTheory Filter Topology
theorem solution (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) :
    let w : ℝ → ℝ := fun x => Real.exp |x| * (1 + x^2)^2
    Integrable (fun x => w x * ‖g x‖) →
    Tendsto (fun L : ℝ => ∫ x : ℝ, (w (x+L) / (Real.exp L * L^4)) • g x)
      atTop (𝓝 (∫ x : ℝ, Real.exp x • g x)) := by
  intro w hint
  obtain ⟨hlim,hbound⟩ := MasulloRH.critical_width_translated_global_gram_density
  apply tendsto_integral_filter_of_dominated_convergence (fun x => 9*(w x * ‖g x‖))
  · apply Eventually.of_forall
    intro L
    have hw : Continuous (fun x : ℝ => w (x+L)/(Real.exp L * L^4)) := by
      dsimp [w]; fun_prop
    exact hw.aestronglyMeasurable.smul hg
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    apply Eventually.of_forall
    intro x
    have hn : 0 ≤ w (x+L)/(Real.exp L * L^4) := by dsimp [w]; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbound x L hL) (norm_nonneg _)
  · exact hint.const_mul 9
  · exact Eventually.of_forall (fun x => (hlim x).smul (tendsto_const_nhds (x := g x)))
