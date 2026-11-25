-- Prove2me | solution 1 for GlobalTheory.SmoothDirections.smoothOfRelativeDimension_of_forall_finrank_derivation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:44.636645+00:00
-- url     : https://prove2.me/submissions/508cc078-2478-4be3-83b2-4140ca87b884

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe
import Theorems.Thm_GlobalTheory_SmoothTangent_finrank_cotangent_le_finrank_derivation
import Theorems.Thm_GlobalTheory_SmoothTangent_le_height_of_forall_minimalPrimes
import Theorems.Thm_GlobalTheory_isSmoothAt_of_finrank_cotangent_le_of_perfectField


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
open GlobalTheory GlobalTheory.SmoothDirections
namespace GlobalTheory.SmoothDirections
theorem _root_.solution (k : Type) [Field k]
    [PerfectField k] (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (d : ℕ)
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (ht : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      Module.finrank K (Derivation k R K) ≤ d) :
    SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast SmoothTangent.le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      exact (SmoothTangent.finrank_cotangent_le_finrank_derivation k m
        (AlgebraicClosure (R ⧸ m))).trans (ht _)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this
end GlobalTheory.SmoothDirections
