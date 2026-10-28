-- Prove2me | solution 1 for ItoLemma.fin_two_compact_support_second_fderiv_uniformContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:07:15.931996+00:00
-- url     : https://prove2.me/submissions/c4649172-d05f-4b63-acf8-3af9ce69f762

import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.UniformSpace.HeineCantor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A continuous Hessian of a compactly supported function is uniformly continuous. -/
theorem solution
    (f : (Fin 2 → ℝ) → ℝ)
    (hs : HasCompactSupport f)
    (h₂ : Continuous (fderiv ℝ (fderiv ℝ f))) :
    UniformContinuous (fderiv ℝ (fderiv ℝ f)) := by
  have hs₁ : HasCompactSupport (fderiv ℝ f) := hs.fderiv ℝ
  have hs₂ : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hs₁.fderiv ℝ
  exact hs₂.uniformContinuous_of_continuous h₂
