-- Prove2me | solution 2 for GlobalTheory.isoTransvection.apply_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:44.13451+00:00
-- url     : https://prove2.me/submissions/284419d9-b996-46ea-a253-fa62fee1455e

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
namespace GlobalTheory.isoTransvection
theorem _root_.solution (b : R) {v : M} (hv : h v x = 0) : isoTransvection h x hx b v = v := by
  simp [apply, hv]
end GlobalTheory.isoTransvection
