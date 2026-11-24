-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_diag_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:41.609036+00:00
-- url     : https://prove2.me/submissions/b295e8aa-09d4-4f39-ae16-ac8a17dbd0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_diag

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
    h (isoTransvection h x hx b v) (isoTransvection h x hx b v)
      = h v v + ((2 * b.re * ‖h v x‖ ^ 2 : ℝ) : ℂ) := by
  rw [form_apply_diag x hx hh, Complex.star_def, Complex.add_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring
end GlobalTheory.isoTransvection
