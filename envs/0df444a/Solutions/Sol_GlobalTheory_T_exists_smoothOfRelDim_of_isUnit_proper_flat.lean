-- Prove2me | solution 1 for GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:10.579095+00:00
-- url     : https://prove2.me/submissions/842b8dd7-a9e7-4d37-b60c-f59376bc0438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothOfRelDimOfIsUnitProperFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothOfRelDimOfIsUnitProperFlatStatement
import Theorems.Thm_GlobalTheory_SmoothNearFibre_exists_smoothOfRelativeDimension_of_isUnit


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | exact GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | (intros; apply GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit <;> assumption)
end _root_.GlobalTheory.T
