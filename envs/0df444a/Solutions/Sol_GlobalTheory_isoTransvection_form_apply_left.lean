-- Prove2me | solution 1 for GlobalTheory.isoTransvection.form_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:09.60475+00:00
-- url     : https://prove2.me/submissions/05570c5a-03eb-4c93-92ce-a51df5bc4d9b

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
theorem _root_.solution (b : R) (u v : M) :
    h (isoTransvection h x hx b u) v = h u v + b * h u x * h x v := by
  simp [apply]
end GlobalTheory.isoTransvection
