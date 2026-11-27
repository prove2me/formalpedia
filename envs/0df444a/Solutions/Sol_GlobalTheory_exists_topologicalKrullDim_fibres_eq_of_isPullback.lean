-- Prove2me | solution 1 for GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:03.61592+00:00
-- url     : https://prove2.me/submissions/10ecd277-f449-4cb9-b399-dbf028552dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
import Theorems.Thm_GlobalTheory_exists_topologicalKrullDim_fibres_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_isEmbedding_and_range_eq_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
namespace GlobalTheory
theorem _root_.solution
    (K k : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    {Y₀ Y₁ : Scheme.{u}} {i₀ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Spec (.of k)} {i₁ : Y₁ ⟶ Y}
    {p₁ : Y₁ ⟶ Spec (.of K)}
    (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap O K)))) :
    ∃ d : ℕ, topologicalKrullDim Y₁ = d ∧ ∀ Z ∈ irreducibleComponents Y₀,
      topologicalKrullDim Z = d ∧
        ∀ z, IsGenericPoint z Z → ringKrullDim (Y.presheaf.stalk (i₀ z)) = 1 := by
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap O k)) hk
  have := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
  obtain ⟨e₀, r₀⟩ := isEmbedding_and_range_eq_of_isPullback f h₀
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f h₁
  have hr₀ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap O k))) = {closedPoint O} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap O k) x.asIdeal = maximalIdeal O
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  have hr₁ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
      {genericPoint (Spec (.of O))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap O K) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  rw [hr₀] at r₀
  rw [hr₁] at r₁
  obtain ⟨d, hd₁, hd₀⟩ := exists_topologicalKrullDim_fibres_eq_of_isEmbedding f e₀ r₀ e₁ r₁
  exact ⟨d, hd₁, fun Z hZ ↦ ⟨hd₀ Z hZ, fun z hz ↦
    ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents f e₀ r₀ hZ hz⟩⟩
end GlobalTheory
