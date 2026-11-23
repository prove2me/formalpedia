-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:28.185399+00:00
-- url     : https://prove2.me/submissions/849b1318-eb5a-4ea8-8ef0-8ea2211d4587

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
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
namespace GlobalTheory.isoTransvection
theorem _root_.solution (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h u (isoTransvection h x hx b v) = h u v + star b * h u x * h x v := by
  have : h x v = star (h v x) := hh v x
  simp only [apply, map_add, LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', smul_eq_mul, this]
  ring
end GlobalTheory.isoTransvection
