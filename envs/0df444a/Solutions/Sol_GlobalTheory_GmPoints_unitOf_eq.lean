-- Prove2me | solution 1 for GlobalTheory.GmPoints.unitOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:03.201963+00:00
-- url     : https://prove2.me/submissions/d6786164-e20b-4562-a29b-ee0befd427c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_val
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
theorem _root_.solution (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf w = Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R) w
        (Multiplicative.ofAdd (ULift.up 1))) := by
  ext
  rw [unitOf_val, ← splitTorusPointsEquiv_val]
  rfl
end GlobalTheory.GmPoints
