-- Prove2me | solution 1 for GlobalTheory.PairingLevels.oneGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:02.574616+00:00
-- url     : https://prove2.me/submissions/aec57e68-45c7-4919-a6c1-2bfd917147d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
omit [GrpObj A]
namespace GlobalTheory.PairingLevels
theorem _root_.solution : (LB.oneGen L (Y := Y.left)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
end GlobalTheory.PairingLevels
