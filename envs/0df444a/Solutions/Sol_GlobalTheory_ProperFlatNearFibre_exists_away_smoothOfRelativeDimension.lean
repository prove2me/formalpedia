-- Prove2me | solution 1 for GlobalTheory.ProperFlatNearFibre.exists_away_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:44.526316+00:00
-- url     : https://prove2.me/submissions/159662ab-bb20-458d-babf-aed4c6aeaf91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsOpensSmoothOfRelativeDimensionOfFlat
import Theorems.Thm_GlobalTheory_ProperFlatNearFibre_exists_opens_smoothOfRelativeDimension_of_flat
import Theorems.Thm_GlobalTheory_ProperFlatNearFibre_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_GlobalTheory_VeryDenseFibres_spMap_apply_asIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.ProperFlatNearFibre
namespace GlobalTheory.ProperFlatNearFibre
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩
end GlobalTheory.ProperFlatNearFibre
