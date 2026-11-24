-- Prove2me | solution 1 for GlobalTheory.ThetaTangent.dense_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:50.803256+00:00
-- url     : https://prove2.me/submissions/4da05e41-e2e4-4a2c-95fd-65c377230a2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaTangent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaTangent
theorem _root_.solution [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f)
    (h0 : f ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  rw [mem_closure_iff_frequently]
  by_contra h
  rw [Filter.not_frequently] at h
  apply h0
  have h1 : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := h.mono fun y hy => by simpa using hy
  have := GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hf.differentiableOn
    (differentiableOn_const (0 : ℂ)) (Set.mem_univ x) h1
  funext y
  exact this (Set.mem_univ y)
end GlobalTheory.ThetaTangent
