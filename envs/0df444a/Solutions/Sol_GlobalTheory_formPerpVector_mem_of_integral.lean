-- Prove2me | solution 1 for GlobalTheory.formPerpVector_mem_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:33.205021+00:00
-- url     : https://prove2.me/submissions/5048b94e-c10c-40bb-a34d-96c23b09d806

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
theorem _root_.solution {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ (algebraMap A R).range) {e e' : ι → M} {g : M}
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : formPerpVector h e e' g ∈ L :=
  formPerpVector_mem L h e he' hg (fun a a' => hL _ (he' a') _ (he a))
    fun a => hL _ hg _ (he a)
end GlobalTheory
