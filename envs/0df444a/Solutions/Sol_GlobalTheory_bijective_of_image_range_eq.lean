-- Prove2me | solution 1 for GlobalTheory.bijective_of_image_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:20.755362+00:00
-- url     : https://prove2.me/submissions/b6ef43e3-ba52-4546-b989-43118b794265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
namespace GlobalTheory
theorem _root_.solution {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [Module ℝ V'] [IsScalarTower ℝ ℂ V'] (hdim : Module.finrank ℂ V = Module.finrank ℂ V')
    (h : V →ₗ[ℂ] V') {S : Set V'} (hS : Submodule.span ℝ S = ⊤) (hh : S ⊆ range h) :
    Function.Bijective h := by
  have hs : Function.Surjective h := fun y => by
    have : Submodule.span ℝ S ≤ (LinearMap.range h).restrictScalars ℝ := Submodule.span_le.2 hh
    exact this (hS ▸ Submodule.mem_top)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hs, hs⟩
end GlobalTheory
