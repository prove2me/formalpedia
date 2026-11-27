-- Prove2me | solution 1 for GlobalTheory.isoTransvection.commute_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:34.556266+00:00
-- url     : https://prove2.me/submissions/cbc999a2-0603-4968-8bbf-9f1a42310d12

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
theorem _root_.solution (g : M ≃ₗ[R] M) (hgx : g x = x) (hg : ∀ u, h (g u) x = h u x) (b : R) :
    Commute g (isoTransvection h x hx b) := by
  ext v
  simp [LinearEquiv.mul_apply, apply, hg, hgx]
end GlobalTheory.isoTransvection
