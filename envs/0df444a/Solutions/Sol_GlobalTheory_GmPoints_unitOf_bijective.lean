-- Prove2me | solution 1 for GlobalTheory.GmPoints.unitOf_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:53:22.12991+00:00
-- url     : https://prove2.me/submissions/66d7fd58-04e4-4095-a5a9-8b7e5800dc87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Theorems.Thm_GlobalTheory_GmPoints_evalOne_bijective
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
namespace GlobalTheory.GmPoints
theorem _root_.solution :
    Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) := by
  rw [funext (unitOf_eq (O := O) (R := R))]
  exact (Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv).bijective.comp
    (evalOne_bijective.comp
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)).bijective)
end GlobalTheory.GmPoints
