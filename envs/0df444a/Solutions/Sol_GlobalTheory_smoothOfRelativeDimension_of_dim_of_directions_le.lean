-- Prove2me | solution 1 for GlobalTheory.smoothOfRelativeDimension_of_dim_of_directions_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:29.188039+00:00
-- url     : https://prove2.me/submissions/30b71134-4b24-471b-9226-876c0c2d7ae0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe
import Theorems.Thm_GlobalTheory_SmoothDirections_finrank_derivation_le
import Theorems.Thm_GlobalTheory_SmoothDirections_smoothOfRelativeDimension_of_forall_finrank_derivation_le
import Theorems.Thm_GlobalTheory_exists_affine_chart_over


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
open GlobalTheory
open SmoothDirections
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ),
      LocallyOfFiniteType s →
      (∀ (R : Type) [CommRing R] [Algebra k R] (x : Sp R ⟶ X), IsOpenImmersion x →
        x ≫ s = spMap (algebraMap k R) →
        ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : k →+* K)
        (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
        x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
        (∀ lam : (Fin r → K) →ₗ[K] K,
          spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) →
      SmoothOfRelativeDimension d s := by
  intro k _ _ X s d _ hd ht
  choose A iA aA j hj q hq hjs using exists_affine_chart_over s
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers X (fun x ↦ Sp (A x)) j (fun x ↦ ⟨x, q x, hq x⟩) hj)
    fun (x : X) ↦ ?_
  change SmoothOfRelativeDimension d (j x ≫ s)
  let := iA x
  let := aA x
  have := hj x
  have : Algebra.FiniteType k (A x) := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap k (A x)))).mp (hjs x ▸ inferInstance)
  rw [hjs]
  exact smoothOfRelativeDimension_of_forall_finrank_derivation_le k (A x) d
    (hd _ (j x) (hj x) (hjs x)) fun K _ _ _ _ _ ↦ finrank_derivation_le s (j x) (hjs x) (ht K)
end GlobalTheory
