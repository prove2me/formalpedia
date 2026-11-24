-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.commIsOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:41.694811+00:00
-- url     : https://prove2.me/submissions/ac3cd50c-a13d-4a14-949c-e3dbaf0bf261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_val_prod
import Theorems.Thm_GlobalTheory_CommutatorPairing_val_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L z J →
      commVal θx θy t a z J = gm t.left z ⊤ c := by
  constructor
  · intro h Z t a z J hJ
    have := val_corr hJ h (lift t a).left
    exact mul_inv_eq_iff_eq_mul.2 ((val_prod θx θy t a hJ).symm.trans (this.trans ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (val_prod θy θx t a hJ) (val_const c t a z J)).trans (mul_comm _ _)))))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    have e : 𝟙 (T ⊗ A).left = (lift (fst T A) (snd T A)).left := by rw [lift_fst_snd]; rfl
    rw [e]
    exact (val_prod θx θy _ _ hJ).trans (((mul_inv_eq_iff_eq_mul.1 (h _ (fst T A) (snd T A) y J hJ)).trans
      (mul_comm _ _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_prod θy θx _ _ hJ) (val_const c _ _ y J))).symm)
end GlobalTheory.CommutatorPairing
