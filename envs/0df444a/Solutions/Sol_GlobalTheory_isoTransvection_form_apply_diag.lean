-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:27.016381+00:00
-- url     : https://prove2.me/submissions/b40b8581-f359-45d3-b031-3d175fc5290b

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
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
namespace GlobalTheory.isoTransvection
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b : R) (v : M) :
    h (isoTransvection h x hx b v) (isoTransvection h x hx b v)
      = h v v + (b + star b) * (h v x * star (h v x)) := by
  rw [form_apply_apply x hx hh, hh v x, mul_assoc]
end GlobalTheory.isoTransvection
