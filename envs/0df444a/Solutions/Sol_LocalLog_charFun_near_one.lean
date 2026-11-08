-- Prove2me | solution 1 for LocalLog.charFun_near_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:40:55.707875+00:00
-- url     : https://prove2.me/submissions/89e60bb1-eec1-4754-b307-cf319fde0f8e

import Mathlib.Analysis.Normed.Group.Defs
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
universe u

/-- The value at zero is the limit of a continuous characteristic function. -/
theorem solution
    {E : Type u} [TopologicalSpace E] [Zero E] [SeminormedAddCommGroup E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    Tendsto φ (𝓝 0) (𝓝 1) := by
  rw [← hφ_zero]
  exact hφ_cont.continuousAt.tendsto
