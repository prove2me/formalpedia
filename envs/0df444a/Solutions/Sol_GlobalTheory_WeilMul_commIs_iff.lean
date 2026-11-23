-- Prove2me | solution 1 for GlobalTheory.WeilMul.commIs_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:36.563245+00:00
-- url     : https://prove2.me/submissions/91fdb8a7-8127-41f2-b6ad-53529a9e2408

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_lift_translT
import Theorems.Thm_GlobalTheory_WeilMul_val_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilMul
theorem _root_.solution (hL : L.IsLB) {T : Over S} (V : T.left.Opens) (θx θy : ThetaGrp A L k (overRes V))
    (c : Γ(T.left, ⊤)ˣ) : CommIsOf A L k θx θy (unitRes V c) ↔ CommV θx θy (overResι V) c := by
  have e : ∀ (θ θ' : ThetaGrp A L k (overRes V)) (T' : Over S) (t : T' ⟶ overRes V) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (lift t a).left z J =
        tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := fun θ θ' T' t a z J hJ => by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [← Over.comp_left, lift_translT]; rfl
  constructor
  · intro h T' t a z J hJ
    exact (e θx θy _ t a z J hJ).symm.trans ((val_corr hJ h (lift t a).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ t a z J hJ) (val_const V c t a z J))))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    have i : 𝟙 (overRes V ⊗ A).left = (lift (fst (overRes V) A) (snd (overRes V) A)).left := by
      rw [lift_fst_snd]; rfl
    rw [i]
    exact (e θx θy _ _ _ y J hJ).trans ((h _ _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ _ _ y J hJ) (val_const V c _ _ y J))).symm)
end GlobalTheory.WeilMul
