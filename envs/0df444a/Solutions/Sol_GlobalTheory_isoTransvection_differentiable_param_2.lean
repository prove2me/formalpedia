-- Prove2me | solution 2 for GlobalTheory.isoTransvection.differentiable_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:41.795189+00:00
-- url     : https://prove2.me/submissions/96a62901-61fa-4ff9-9e27-d28eeeff2767

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
theorem _root_.solution (v : W) :
    Differentiable ℂ fun b : ℂ => isoTransvection h x hx b v := by
  simp only [apply]; fun_prop
end GlobalTheory.isoTransvection
