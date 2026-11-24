-- Prove2me | solution 1 for GlobalTheory.perpVector_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:10.09412+00:00
-- url     : https://prove2.me/submissions/11e26742-e024-4f87-bf9b-cd9c77c606d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CommRing A] [Algebra A R]
namespace GlobalTheory
theorem _root_.solution [Module A M] [IsScalarTower A R M] (L : Submodule A M)
    (ε : ι → Module.Dual R M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range)
    (hg : ∀ a, ε a g ∈ (algebraMap A R).range) : perpVector ε e' g ∈ L := by
  choose x hx using he
  choose y hy using hg
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  rw [perpVector, hm, ← RingHom.map_det, ← RingHom.map_adjugate]
  refine L.sub_mem ?_ (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  · rw [algebraMap_smul]; exact L.smul_mem _ hgL
  · rw [← hy, RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul, algebraMap_smul]
    exact L.smul_mem _ (he' a')
end GlobalTheory
