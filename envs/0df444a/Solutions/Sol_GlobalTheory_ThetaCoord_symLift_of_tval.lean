-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.symLift_of_tval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:23.694169+00:00
-- url     : https://prove2.me/submissions/ade22ce8-aff4-45d5-8865-d9fadf1d1ae6

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
import Theorems.Thm_GlobalTheory_GlobalLift_val_powGen
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_id_eq_lift
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_powGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
theorem _root_.solution (hL : L.IsLB) {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T} (hx : θ.pt = x)
    {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen)
    (h₁ : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      ∏ j ∈ Finset.range n, tval θ (lift π ((π ≫ x) ^ j * p)).left z J = 1)
    (h₂ : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      tval θ (lift π ((π ≫ x)⁻¹ * p)).left z J * nval ν (lift π p).left z J *
        (tval θ (lift π p⁻¹).left z J * (nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹) = 1) :
    SymLift A L k n x θ := by
  refine ⟨hx, corr_of_val hL fun y J hJ => ?_, ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_one, SymLiftOdd.id_eq_lift]
    exact (SymLiftOdd.val_powGen θ n hx hJ _).trans (h₁ _ _ y J hJ _)
  · rw [val_one, SymLiftOdd.id_eq_lift]
    exact (SymLiftOdd.val_symGen θ ν hx hJ _).trans (h₂ _ _ y J hJ _)
end GlobalTheory.ThetaCoord
