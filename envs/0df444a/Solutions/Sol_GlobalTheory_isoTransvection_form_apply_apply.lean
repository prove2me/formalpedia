-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:41.182075+00:00
-- url     : https://prove2.me/submissions/46cd0c48-4ac1-4cee-9edf-4f8094571dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_left
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_right

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
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
namespace GlobalTheory.isoTransvection
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v := by
  rw [form_apply_left, form_apply_right x hx hh, form_self_apply]
  ring
end GlobalTheory.isoTransvection
