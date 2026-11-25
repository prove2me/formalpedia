-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.exists_symLift_act_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:36.278481+00:00
-- url     : https://prove2.me/submissions/1a65c508-d2df-4514-8387-f6b9013ffcd7

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
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_negT
import Theorems.Thm_GlobalTheory_ThetaCoord_prod_tval
import Theorems.Thm_GlobalTheory_ThetaCoord_symLift_of_tval
import Theorems.Thm_GlobalTheory_ThetaCoord_sv_act
import Theorems.Thm_GlobalTheory_CommPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_GlobalTheory_GlobalLift_exists_neg_pull
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_id_eq_lift
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_negT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_GlobalTheory_VVRank_isTwistPull_of_sv
import Theorems.Thm_GlobalTheory_VVRank_sv_pullS
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
theorem _root_.solution (hL : L.IsLB) {n : ℕ} (h : T' ⟶ T) {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (H : SymLift A L k n x θ) : ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧
      ∀ s s', IsActOf A L k θ s s' → IsActOf A L k θ' (pullS A k h s) (pullS A k h s') := by
  obtain ⟨θ', e, v⟩ := CommPairing.exists_pull hL h θ
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have e₀ : ∀ (T₀ : Over S) (π : T₀ ⟶ T') (p : T₀ ⟶ A), (lift π p).left ≫ (h ▷ A).left = (lift (π ≫ h) p).left :=
    fun T₀ π p => by rw [← Over.comp_left, lift_whiskerRight]
  refine ⟨θ', symLift_of_tval hL (e.trans (by rw [H.pt_eq])) hν' (fun T₀ π z J hJ p => ?_) (fun T₀ π z J hJ p => ?_),
    fun s s' hs => isTwistPull_of_sv A hL θ'.isGen fun z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, e₀, ← Category.assoc]
    exact prod_tval H _ hJ p
  · have q := val_corr hJ hs (lift (π ≫ h) p).left
    rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at q
    simp only [v _ _ z J hJ, w _ _ z J hJ, e₀, ← Category.assoc]
    exact q
  · have q := v _ (lift (fst T' A) (snd T' A)).left z J hJ
    rw [SymLiftOdd.id_eq_lift, lift_translT, sv_pullS A k h _ _ z hJ, sv_pullS A k h _ _ z hJ, e₀, e₀,
      sv_act rfl hs _ hJ]
    rw [e₀] at q
    exact congrArg₂ (· * ·) (congrArg Units.val q.symm) (by rw [e, Category.assoc])
end GlobalTheory.ThetaCoord
