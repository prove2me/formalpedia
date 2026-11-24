-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.smooth_away_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:41.454881+00:00
-- url     : https://prove2.me/submissions/560449e0-7dbc-437a-9c72-1df316d75dc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π))) (f : B) :
    Algebra.Smooth R (Localization.Away (algebraMap R (Localization.Away f) π)) := by
  let p := algebraMap R B π
  let T := Localization.Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth (Localization.Away p) T := Algebra.Smooth.of_isLocalization_Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth R T := Algebra.Smooth.comp R (Localization.Away p) T
  haveI : IsLocalization.Away (f * p) T := inferInstance
  haveI : IsLocalization.Away (algebraMap B (Localization.Away f) p) (Localization.Away (algebraMap R (Localization.Away f) π)) := by
    rw [← IsScalarTower.algebraMap_apply]; infer_instance
  haveI : IsLocalization.Away (f * p) (Localization.Away (algebraMap R (Localization.Away f) π)) :=
    IsLocalization.Away.mul' (Localization.Away f) _ f p
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * p)) T
    (Localization.Away (algebraMap R (Localization.Away f) π))).restrictScalars R)
end GlobalTheory.SS.Smoothening
