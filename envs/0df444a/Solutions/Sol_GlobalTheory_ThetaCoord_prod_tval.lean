-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.prod_tval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:21.29194+00:00
-- url     : https://prove2.me/submissions/ef5b5803-14d4-436b-ab30-b591747bdff5

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
import Theorems.Thm_GlobalTheory_GlobalLift_val_powGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_powGen
import Theorems.Thm_GlobalTheory_WeilMul_lift_translT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    ∏ j ∈ Finset.range n, tval θ (lift π ((π ≫ x) ^ j * p)).left z J = 1 := by
  have q := val_corr hJ H.pow_eq (lift π p).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q
  rw [Finset.prod_range]
  refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
  rw [lift_translT, H.pt_eq, MonObj.comp_pow]
end GlobalTheory.ThetaCoord
