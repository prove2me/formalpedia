-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_apply_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:40.172026+00:00
-- url     : https://prove2.me/submissions/74e3772a-0d7d-41c1-a199-835f1385ef2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_apply

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
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (u v : W) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (2 * b.re : ℝ) * h u x * h x v := by
  rw [form_apply_apply x hx hh, Complex.star_def, Complex.add_conj]
end GlobalTheory.isoTransvection
