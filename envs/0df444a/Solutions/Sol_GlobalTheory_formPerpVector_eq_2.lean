-- Prove2me | solution 2 for GlobalTheory.formPerpVector_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:06.370246+00:00
-- url     : https://prove2.me/submissions/2dfb88da-88d0-45f5-9e03-9c29b734bb81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}
namespace GlobalTheory
theorem _root_.solution (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) :
    formPerpVector h e e' g = (formPairMatrix h e e').det • g
      - ∑ a, ∑ a', ((formPairMatrix h e e').adjugate a a' * h g (e a)) • e' a' := rfl
end GlobalTheory
