-- Prove2me | solution 1 for Kyprianou.Ch04.generatorAbsoluteJumpContinuityOnCompact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:06:00.387136+00:00
-- url     : https://prove2.me/submissions/a4ca76d4-55de-47a3-b919-f7bfb57f7813

import Mathlib
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Local integrable jump envelopes imply continuity of the absolute jump mass. -/
theorem solution (nu : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x) :
    Continuous (fun y => ∫ x, ‖f (y+x)-f y‖ ∂nu) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨r,hr,b,hbi,hb⟩ := hdom y
  have hc : ContinuousOn (fun z => ∫ x, ‖f (z+x)-f z‖ ∂nu)
      (Set.Icc (y-r) (y+r)) := by
    apply continuousOn_of_dominated
    · intro z hz
      exact ((hf.comp (continuous_const.add continuous_id)).sub continuous_const).norm.aestronglyMeasurable
    · intro z hz
      simpa only [Real.norm_eq_abs,abs_abs] using hb z hz
    · exact hbi
    · exact Eventually.of_forall fun x => ((hf.comp (continuous_id.add continuous_const)).sub hf).norm.continuousOn
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
