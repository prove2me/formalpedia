-- Prove2me | solution 2 for GlobalTheory.isoTransvection.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:13.726882+00:00
-- url     : https://prove2.me/submissions/69ad3d11-2f02-489e-8c6d-fb4189f963e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvectionHom_ofAdd

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
namespace GlobalTheory.isoTransvection
theorem _root_.solution (b : R) (n : ℕ) :
    isoTransvection h x hx b ^ n = isoTransvection h x hx (n * b) := by
  rw [← isoTransvectionHom_ofAdd, ← map_pow, ← ofAdd_nsmul, isoTransvectionHom_ofAdd,
    nsmul_eq_mul]
end GlobalTheory.isoTransvection
