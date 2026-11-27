-- Prove2me | solution 1 for GlobalTheory.isoTransvection.map_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:05.422101+00:00
-- url     : https://prove2.me/submissions/8e85de3d-3a5a-4487-8daa-46ef99322d17

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
variable (h)
namespace GlobalTheory.isoTransvection
theorem _root_.solution {R' M' : Type*} [CommRing R'] [StarRing R'] [AddCommGroup M'] [Module R' M']
    {φ : R →+* R'} (j : M →ₛₗ[φ] M') (h' : M' →ₗ[R'] M' →ₗ⋆[R'] R')
    (hx' : h' (j x) (j x) = 0) (b : R) (v : M) (hj : h' (j v) (j x) = φ (h v x)) :
    j (isoTransvection h x hx b v) = isoTransvection h' (j x) hx' (φ b) (j v) := by
  simp [apply, hj]
end GlobalTheory.isoTransvection
