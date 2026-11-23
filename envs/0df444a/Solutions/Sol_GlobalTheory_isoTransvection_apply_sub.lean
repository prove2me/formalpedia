-- Prove2me | solution 1 for GlobalTheory.isoTransvection.apply_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:43.199006+00:00
-- url     : https://prove2.me/submissions/d133c41c-37c3-4896-95e0-da4758bee420

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
theorem _root_.solution (b : R) (v : M) : isoTransvection h x hx b v - v = (b * h v x) • x := by
  rw [apply, add_sub_cancel_left]
end GlobalTheory.isoTransvection
