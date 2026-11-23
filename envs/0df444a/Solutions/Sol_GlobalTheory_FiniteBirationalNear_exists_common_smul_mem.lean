-- Prove2me | solution 1 for GlobalTheory.FiniteBirationalNear.exists_common_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:46.138386+00:00
-- url     : https://prove2.me/submissions/d8348bb8-831b-44c9-bbb7-a5cb8b7356b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.FiniteBirationalNear
namespace GlobalTheory.FiniteBirationalNear
theorem _root_.solution {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (S : Submonoid A) {N : Submodule A M} (hN : N.FG) (N' : Submodule A M)
    (h : ∀ m ∈ N, ∃ s ∈ S, s • m ∈ N') : ∃ s ∈ S, ∀ m ∈ N, s • m ∈ N' := by
  classical
  obtain ⟨T, rfl⟩ := hN
  choose! s hs hs' using h
  refine ⟨∏ t ∈ T, s t, prod_mem fun t ht => hs t (Submodule.subset_span ht), ?_⟩
  have : Submodule.span A (T : Set M) ≤ N'.comap ((∏ t ∈ T, s t) • LinearMap.id) := by
    refine Submodule.span_le.2 fun t ht => ?_
    change (∏ t ∈ T, s t) • t ∈ N'
    rw [← Finset.prod_erase_mul T s ht, mul_smul]
    exact N'.smul_mem _ (hs' t (Submodule.subset_span ht))
  exact fun m hm => this hm
end GlobalTheory.FiniteBirationalNear
