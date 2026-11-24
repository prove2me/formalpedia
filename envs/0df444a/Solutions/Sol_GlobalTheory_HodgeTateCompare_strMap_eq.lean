-- Prove2me | solution 1 for GlobalTheory.HodgeTateCompare.strMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:47.194674+00:00
-- url     : https://prove2.me/submissions/aa2a8727-685f-45c8-b8f6-46008fc81c29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Theorems.Thm_GlobalTheory_AugCot_map_comp


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
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
noncomputable section
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
namespace GlobalTheory.HodgeTateCompare
theorem _root_.solution : strMap G =
    StructureSheaf.toStalk O (G.hom (origin G)) ≫ G.hom.stalkMap (origin G) := by
  apply Spec.map_injective
  have e : (Spec (CommRingCat.of O)).fromSpecStalk (G.hom (origin G)) =
      Spec.map (StructureSheaf.toStalk O (G.hom (origin G))) := Spec.fromSpecStalk_eq' _ _
  refine (spec_strMap G).trans ?_
  refine (Scheme.SpecMap_stalkMap_fromSpecStalk G.hom (x := origin G)).symm.trans ?_
  rw [e]
  exact (Spec.map_comp _ _).symm
end GlobalTheory.HodgeTateCompare
