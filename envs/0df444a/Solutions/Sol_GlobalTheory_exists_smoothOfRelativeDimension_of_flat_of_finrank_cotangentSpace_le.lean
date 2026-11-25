-- Prove2me | solution 1 for GlobalTheory.exists_smoothOfRelativeDimension_of_flat_of_finrank_cotangentSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:12:19.447298+00:00
-- url     : https://prove2.me/submissions/b1111cc2-3584-4ae5-a5f7-17643621e481

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Theorems.Thm_GlobalTheory_exists_affine_chart_over
import Theorems.Thm_GlobalTheory_exists_affine_chart_of_isPullback
import Theorems.Thm_GlobalTheory_topologicalKrullDim_closure_eq_ringKrullDim_quotient
import Theorems.Thm_GlobalTheory_closure_mem_irreducibleComponents_of_mem_minimalPrimes

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
open AlgebraicGeometry CategoryTheory Topology
variable (V K k : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  [Field k] [Algebra V k] (hk : Function.Surjective (algebraMap V k))
  {X X₀ X₁ : Scheme.{u}} {f : X ⟶ Spec (.of V)} [LocallyOfFiniteType f] [Flat f]
  {i₀ : X₀ ⟶ X} {p₀ : X₀ ⟶ Spec (.of k)} {i₁ : X₁ ⟶ X} {p₁ : X₁ ⟶ Spec (.of K)}
  (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap V k))))
  (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
include hk h₀ h₁
namespace GlobalTheory
theorem _root_.solution {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X₁, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z)
    (x : X₀) (hxc : IsClosed ({x} : Set X₀))
    (hx : Module.finrank (ResidueField (X₀.presheaf.stalk x))
      (CotangentSpace (X₀.presheaf.stalk x)) ≤ d) :
    (∃ U : X.Opens, i₀ x ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f)) ∧
      IsRegularLocalRing (X₀.presheaf.stalk x) ∧ ringKrullDim (X₀.presheaf.stalk x) = d ∧
      Module.finrank (ResidueField (X₀.presheaf.stalk x))
        (CotangentSpace (X₀.presheaf.stalk x)) = d := by
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f (i₀ x)
  have : Algebra.FiniteType V A := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap V A))).mp (hj ▸ inferInstance)
  have : Module.Flat V A := RingHom.flat_algebraMap_iff.mp <|
    (HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (algebraMap V A))).mp (hj ▸ inferInstance)
  have : LocallyOfFiniteType p₁ := MorphismProperty.of_isPullback h₁ ‹_›
  obtain ⟨j₀, _, H₀⟩ := exists_affine_chart_of_isPullback h₀ j hj
  obtain ⟨j₁, _, -⟩ := exists_affine_chart_of_isPullback h₁ j hj
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H₀ x q hq.symm
  have hmax : y.asIdeal.IsMaximal := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp ?_
    have := hxc.preimage j₀.continuous
    rwa [← Set.image_singleton, j₀.isOpenEmbedding.injective.preimage_image] at this
  have hd' (p) (hp : p ∈ minimalPrimes (K ⊗[V] A)) :
      (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p) :=
    (hd _ (closure_mem_irreducibleComponents_of_mem_minimalPrimes j₁ ⟨p, hp.1.1⟩ hp)).trans_eq
      (topologicalKrullDim_closure_eq_ringKrullDim_quotient p₁ j₁ ⟨p, hp.1.1⟩)
  let e : Localization.AtPrime y.asIdeal ≃+* X₀.presheaf.stalk (j₀ y) :=
    (asIso (j₀.stalkMap y) ≪≫ Spec.stalkIso (.of (k ⊗[V] A)) y).commRingCatIsoToRingEquiv.symm
  let : Algebra (k ⊗[V] A) (X₀.presheaf.stalk (j₀ y)) :=
    (e.toRingHom.comp (algebraMap _ _)).toAlgebra
  have : IsLocalization.AtPrime (X₀.presheaf.stalk (j₀ y)) y.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl
      ({ e with commutes' _ := rfl } : Localization.AtPrime y.asIdeal ≃ₐ[k ⊗[V] A] _)
  obtain ⟨-, ⟨g, hg, hs⟩, h⟩ := isSmoothAt_of_flat_of_finrank_cotangentSpace_le V K hd' _
    (TensorProduct.mk_surjective V A k hk) (ker_includeRight_of_surjective V k hk) y.asIdeal _ hx
  refine ⟨?_, h⟩
  let j' := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) ≫ j
  have hs' : SmoothOfRelativeDimension d (j' ≫ f) := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hs)
  refine ⟨j'.opensRange, ?_, ?_⟩
  · obtain ⟨t, ht⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ g, ← hy]
      exact hg
    refine ⟨t, ?_⟩
    rw [← hq, ← ht]
    rfl
  · rw [← j'.isoOpensRange_inv_comp, Category.assoc]
    have := smoothOfRelativeDimension_comp 0 d j'.isoOpensRange.inv (j' ≫ f)
    rwa [zero_add] at this
end GlobalTheory
