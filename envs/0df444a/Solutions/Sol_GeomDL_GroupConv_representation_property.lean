-- Prove2me | solution 1 for GeomDL.GroupConv.representation_property
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:33:52.04399+00:00
-- url     : https://prove2.me/submissions/5418369a-8f53-47c6-85e9-2b13566434ea

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

open GeomDL.GroupConv

universe u v
theorem solution {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    (h g : G) (θ : Ω → ℝ) :
    signalAction h⁻¹ (signalAction g θ) = signalAction (h⁻¹ * g) θ := by
  funext x
  simp [signalAction, mul_smul]
