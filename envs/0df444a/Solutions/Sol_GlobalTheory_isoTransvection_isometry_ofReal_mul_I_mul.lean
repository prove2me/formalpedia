-- Prove2me | solution 1 for GlobalTheory.isoTransvection.isometry_ofReal_mul_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:59.624705+00:00
-- url     : https://prove2.me/submissions/a1687bf3-8688-4d7a-97e2-94fd08753754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_isometry_of_re
import Theorems.Thm_GlobalTheory_isoTransvection_re_mul_I_mul

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
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b s : ℝ) (u v : W) :
    h (isoTransvection h x hx (b * (Complex.I * s)) u)
      (isoTransvection h x hx (b * (Complex.I * s)) v) = h u v :=
  isometry_of_re x hx hh (by rw [re_mul_I_mul]; simp) u v
end GlobalTheory.isoTransvection
