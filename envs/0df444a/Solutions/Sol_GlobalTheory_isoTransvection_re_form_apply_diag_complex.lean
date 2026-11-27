-- Prove2me | solution 1 for GlobalTheory.isoTransvection.re_form_apply_diag_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:18.991341+00:00
-- url     : https://prove2.me/submissions/68e44004-7f9f-463d-b4af-ba2f94354b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_diag_complex

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
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (v : W) :
    (h (isoTransvection h x hx b v) (isoTransvection h x hx b v)).re
      = (h v v).re + 2 * b.re * ‖h v x‖ ^ 2 := by
  rw [form_apply_diag_complex x hx hh, Complex.add_re, Complex.ofReal_re]
end GlobalTheory.isoTransvection
