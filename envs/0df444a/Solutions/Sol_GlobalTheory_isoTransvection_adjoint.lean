-- Prove2me | solution 1 for GlobalTheory.isoTransvection.adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:42.746586+00:00
-- url     : https://prove2.me/submissions/85b2bf1f-8672-4cd3-8c96-22c17a7dbc24

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
    h (isoTransvection h x hx b u) v = h u (isoTransvection h x hx (star b) v) := by
  rw [form_apply_left, form_apply_right x hx hh, star_star]
end GlobalTheory.isoTransvection
