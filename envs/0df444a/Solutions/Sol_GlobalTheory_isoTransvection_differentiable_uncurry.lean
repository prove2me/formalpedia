-- Prove2me | solution 1 for GlobalTheory.isoTransvection.differentiable_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:53.406004+00:00
-- url     : https://prove2.me/submissions/2aa26b19-32e9-4152-a01a-20e60ebb7008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_analyticOnNhd_uncurry

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
    Differentiable ℂ fun p : ℂ × W => isoTransvection h x hx p.1 p.2 :=
  fun p => (analyticOnNhd_uncurry h x hx p (Set.mem_univ p)).differentiableAt
end GlobalTheory.isoTransvection
