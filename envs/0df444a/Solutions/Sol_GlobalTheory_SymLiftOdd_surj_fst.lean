-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.surj_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:47.482056+00:00
-- url     : https://prove2.me/submissions/b352a2a1-9797-476e-984a-c1b2db9b24ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


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
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have h1 : Function.Surjective (snd A T).left.appTop.hom := (hG _ _ (TLinPf.isAb_pullback T.hom A hA)).2
  have h2 : Function.Surjective (lift (snd T A) (fst T A)).left.appTop.hom := by
    have e : (lift (snd T A) (fst T A)).left ≫ (lift (snd A T) (fst A T)).left = 𝟙 _ :=
      congrArg (fun q => q.left) (show lift (snd T A) (fst T A) ≫ lift (snd A T) (fst A T) = 𝟙 _ by ext <;> simp)
    intro v
    refine ⟨(lift (snd A T) (fst A T)).left.appTop.hom v, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
    simp
  have e : (fst T A).left = (lift (snd T A) (fst T A)).left ≫ (snd A T).left := by
    rw [← Over.comp_left, lift_snd]
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact h2.comp h1
end GlobalTheory.SymLiftOdd
