-- Prove2me | solution 1 for GlobalTheory.T.exists_localDerivation_of_dualNumber_thickening
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:08:03.799406+00:00
-- url     : https://prove2.me/submissions/2645d888-2cd4-41e5-ab22-22bad59dedc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickening
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickeningStatement
import Theorems.Thm_GlobalTheory_KS_EpsDer_exists_locDer


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (Φ : Y' ⟶ X), j ≫ Φ = m → Φ ≫ p = π ≫ spMap xD → ∃ d, LocDer q p m (fun r => (xD r).snd) ⊤ d ∧ ∀ (y : Sp ℂ ⟶ Y) (yt : Sp (DualNumber ℂ) ⟶ Y'), yt ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y → yt ≫ π = 𝟙 _ → ∀ (W : X.Opens) (h : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  first | exact @GlobalTheory.KS.EpsDer.exists_locDer | exact GlobalTheory.KS.EpsDer.exists_locDer | (intros; apply GlobalTheory.KS.EpsDer.exists_locDer <;> assumption)
end _root_.GlobalTheory.T
