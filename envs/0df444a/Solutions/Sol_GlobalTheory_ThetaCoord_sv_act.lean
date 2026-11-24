-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.sv_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:18.232825+00:00
-- url     : https://prove2.me/submissions/bbec90ea-3608-406d-959b-d18dd2a7da8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_translT
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull
import Theorems.Thm_GlobalTheory_WeilMul_lift_translT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}
namespace GlobalTheory.ThetaCoord
theorem _root_.solution {θ : ThetaGrp A L k T} {x : T ⟶ A} (hx : θ.pt = x) {s s' : LB.Sec (LPow A L k T)}
    (H : IsActOf A L k θ s s') (π : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    sv A s' (lift π p).left z J = (tval θ (lift π p).left z J).val * sv A s (lift π ((π ≫ x) * p)).left z J := by
  rw [← hx, ← lift_translT]
  exact sv_of_isTwistPull A H _ z hJ
end GlobalTheory.ThetaCoord
