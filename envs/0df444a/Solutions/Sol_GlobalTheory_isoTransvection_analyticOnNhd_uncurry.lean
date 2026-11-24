-- Prove2me | solution 1 for GlobalTheory.isoTransvection.analyticOnNhd_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:38.115662+00:00
-- url     : https://prove2.me/submissions/3c32eb34-1a64-4a6d-859f-15744ccc07d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.isoTransvection
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)
namespace GlobalTheory.isoTransvection
theorem _root_.solution [FiniteDimensional ℂ W] :
    AnalyticOnNhd ℂ (fun p : ℂ × W => isoTransvection h x hx p.1 p.2) Set.univ := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  let f : W →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (h.flip x)
  have : (fun p : ℂ × W => isoTransvection h x hx p.1 p.2)
      = fun p : ℂ × W => p.2 + (p.1 * f p.2) • x := rfl
  rw [this]
  intro p _
  exact analyticAt_snd.add
    ((analyticAt_fst.mul ((f.analyticAt _).comp analyticAt_snd)).smul analyticAt_const)
end GlobalTheory.isoTransvection
