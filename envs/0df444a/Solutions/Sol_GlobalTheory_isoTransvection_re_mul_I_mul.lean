-- Prove2me | solution 1 for GlobalTheory.isoTransvection.re_mul_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:45.232035+00:00
-- url     : https://prove2.me/submissions/a064eb22-76d3-4efc-b749-a4e1588604ef

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)
namespace GlobalTheory.isoTransvection
theorem _root_.solution (b : ℂ) (s : ℝ) : (b * (Complex.I * s)).re = -s * b.im := by
  simp; ring
end GlobalTheory.isoTransvection
