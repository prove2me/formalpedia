-- Prove2me | solution 1 for GlobalTheory.exists_invariant_mem_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:39.770404+00:00
-- url     : https://prove2.me/submissions/71135440-8ed0-400c-a19e-df2cfa555711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution (q : Ideal A) [hq : q.IsPrime] (I : Ideal A)
    (h : ∀ g : G, ¬ I ≤ g • q) : ∃ t ∈ I, (∀ g : G, g • t = t) ∧ t ∉ q := by
  classical
  cases nonempty_fintype G
  have : ¬ (I : Set A) ⊆ ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G), ((g • q : Ideal A) : Set A) := by
    rw [Ideal.subset_union_prime 1 1 (fun g _ _ _ ↦ inferInstance)]
    simpa using h
  obtain ⟨s, hsI, hs⟩ := Set.not_subset.mp this
  simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
    not_exists] at hs
  refine ⟨∏ g : G, g • s, ?_, fun g ↦ Finset.smul_prod_perm s g, fun hmem ↦ ?_⟩
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), one_smul]
    exact I.mul_mem_right _ hsI
  · obtain ⟨g, -, hg⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hs g⁻¹ (by rwa [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv])
end GlobalTheory
