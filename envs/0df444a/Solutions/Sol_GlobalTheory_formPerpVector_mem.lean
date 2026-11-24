-- Prove2me | solution 1 for GlobalTheory.formPerpVector_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:35.045288+00:00
-- url     : https://prove2.me/submissions/52db9974-82d0-4aed-bfcb-d9f4d7e0775c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_perpVector_mem

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
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M}
    {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ (algebraMap A R).range)
    (hg : ∀ a, h g (e a) ∈ (algebraMap A R).range) : formPerpVector h e e' g ∈ L :=
  perpVector_mem L (fun a => h.flip (e a)) he' hgL he hg
end GlobalTheory
