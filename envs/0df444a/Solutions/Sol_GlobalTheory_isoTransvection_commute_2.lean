-- Prove2me | solution 2 for GlobalTheory.isoTransvection.commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:35.79537+00:00
-- url     : https://prove2.me/submissions/51cc5264-4894-421d-bae8-c42155a8616c

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
theorem _root_.solution (b b' : R) :
    Commute (isoTransvection h x hx b) (isoTransvection h x hx b') := by
  rw [Commute, SemiconjBy, mul, mul, add_comm]
end GlobalTheory.isoTransvection
