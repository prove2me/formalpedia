-- Prove2me | solution 1 for GlobalTheory.isoTransvection.differentiable_toContinuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:44.205863+00:00
-- url     : https://prove2.me/submissions/af89f511-d18d-428d-b491-246b6e271dcb

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
    Differentiable ℂ fun b : ℂ =>
      LinearMap.toContinuousLinearMap (isoTransvection h x hx b : W →ₗ[ℂ] W) := by
  let f : W →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (h.flip x)
  have : (fun b : ℂ => LinearMap.toContinuousLinearMap (isoTransvection h x hx b : W →ₗ[ℂ] W))
      = fun b : ℂ => ContinuousLinearMap.id ℂ W + b • f.smulRight x := by
    ext b v
    simp [apply, f, smul_smul]
  rw [this]
  fun_prop
end GlobalTheory.isoTransvection
