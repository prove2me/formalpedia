-- Prove2me | solution 1 for GlobalTheory.formPerpVector_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:12.564803+00:00
-- url     : https://prove2.me/submissions/9610f44c-5807-46ee-bdd2-e0c5fe133510

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_formPerpVector_mem

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
theorem _root_.solution (A : Subring R) (L : Submodule A M)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ A) (hg : ∀ a, h g (e a) ∈ A) :
    formPerpVector h e e' g ∈ L :=
  formPerpVector_mem L h e he' hgL (fun a a' => ⟨⟨_, he a a'⟩, rfl⟩) fun a => ⟨⟨_, hg a⟩, rfl⟩
end GlobalTheory
