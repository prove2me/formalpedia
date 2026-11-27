-- Prove2me | solution 1 for GlobalTheory.isoTransvection.conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:38.269806+00:00
-- url     : https://prove2.me/submissions/8a00b2c8-edac-4bff-951d-f1124bef5ee1

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
theorem _root_.solution (g : M ≃ₗ[R] M) (hg : ∀ u v, h (g u) (g v) = h u v) (b : R)
    (hgx : h (g x) (g x) = 0) :
    g * isoTransvection h x hx b * g⁻¹ = isoTransvection h (g x) hgx b := by
  rw [mul_inv_eq_iff_eq_mul]
  ext v
  simp [LinearEquiv.mul_apply, apply, hg]
end GlobalTheory.isoTransvection
