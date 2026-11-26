-- Prove2me | solution 1 for Kyprianou.Ch04.generatorJumpContinuityOnCompact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:14.889341+00:00
-- url     : https://prove2.me/submissions/0e7a93e4-bf4f-4004-bd38-0fabed685357

import Mathlib
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Local integrable jump envelopes imply continuity of the signed generator. -/
theorem solution (nu : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x) :
    Continuous (fun y => ∫ x, (f (y+x)-f y) ∂nu) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨r,hr,b,hbi,hb⟩ := hdom y
  have hc : ContinuousOn (fun z => ∫ x, (f (z+x)-f z) ∂nu)
      (Set.Icc (y-r) (y+r)) := by
    apply continuousOn_of_dominated
    · intro z hz
      exact ((hf.comp (continuous_const.add continuous_id)).sub continuous_const).aestronglyMeasurable
    · exact hb
    · exact hbi
    · exact Eventually.of_forall fun x => ((hf.comp (continuous_id.add continuous_const)).sub hf).continuousOn
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
