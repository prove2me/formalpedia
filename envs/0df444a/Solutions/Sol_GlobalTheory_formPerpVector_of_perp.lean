-- Prove2me | solution 1 for GlobalTheory.formPerpVector_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:28.569224+00:00
-- url     : https://prove2.me/submissions/b175002a-f26f-44de-8b7e-6f8abd9805c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_perpVector_of_apply_eq_zero

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
theorem _root_.solution (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) {g : M}
    (hg : ∀ a, h g (e a) = 0) : formPerpVector h e e' g = (formPairMatrix h e e').det • g :=
  perpVector_of_apply_eq_zero (fun a => h.flip (e a)) e' hg
end GlobalTheory
