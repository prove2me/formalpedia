-- Prove2me | solution 1 for GlobalTheory.EpsThick.isPullback_special
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:03.242043+00:00
-- url     : https://prove2.me/submissions/9d839e13-2e47-43ab-86df-51169d50804f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure

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
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}
namespace GlobalTheory.EpsThick
theorem _root_.solution (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine (IsPullback.of_bot ?_ h₂.symm H.flip).flip
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [h₁, this]
  exact IsPullback.of_vert_isIso ⟨by simp⟩
end GlobalTheory.EpsThick
