-- Prove2me | solution 1 for GlobalTheory.isoTransvection.differentiable_param
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:28:23.07381+00:00
-- url     : https://prove2.me/submissions/d50d856e-deab-4b55-a791-e9e47d671dd5

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
theorem _root_.solution (v : W) :
    Differentiable ℂ fun b : ℂ => isoTransvection h x hx b v := by
  simp only [GlobalTheory.isoTransvection.apply]
  fun_prop

