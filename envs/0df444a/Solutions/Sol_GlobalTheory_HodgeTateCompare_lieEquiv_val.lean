-- Prove2me | solution 1 for GlobalTheory.HodgeTateCompare.lieEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:26.082716+00:00
-- url     : https://prove2.me/submissions/0e65432e-c9f1-4cc0-996b-6f591f76b416

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective

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
variable {O : Type} [CommRing O] [IsLocalRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
variable {G}
namespace GlobalTheory.HodgeTateCompare
theorem _root_.solution (v : Lie G) : (lieEquiv G v).1 = tangentPt v := rfl
end GlobalTheory.HodgeTateCompare
