-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:55.891671+00:00
-- url     : https://prove2.me/submissions/98c3a076-8028-40f9-b94d-1533c89c6bd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_GlobalTheory_PairingLevels_oneGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
namespace Rep
theorem _root_.solution : Rep L (Y := Y) 0 (fun _ _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, oneGen_isGen, Fintype.sum_empty _, fun _ _ _ _ _ => val_one _⟩
end Rep
end GlobalTheory.PairingLevels
