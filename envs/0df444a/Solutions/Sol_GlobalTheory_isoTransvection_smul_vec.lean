-- Prove2me | solution 1 for GlobalTheory.isoTransvection.smul_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:20.731938+00:00
-- url     : https://prove2.me/submissions/dc4e164d-1dc9-4c4a-81ea-fdf8dc81a294

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
theorem _root_.solution (a b : R) (hax : h (a • x) (a • x) = 0 := by simp [*]) :
    isoTransvection h (a • x) hax b = isoTransvection h x hx (b * (a * star a)) := by
  ext v
  simp only [apply, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, smul_smul]
  congr 2; ring
end GlobalTheory.isoTransvection
