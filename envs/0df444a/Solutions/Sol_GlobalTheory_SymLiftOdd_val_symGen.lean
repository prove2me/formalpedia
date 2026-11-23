-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.val_symGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:42.996811+00:00
-- url     : https://prove2.me/submissions/c7d684ce-4767-420d-976b-7e01536b533c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_negT
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (symGen A L k θ nu) (lift (fst T A) m).left y J =
      thetaVal θ y J ((fst T A ≫ x)⁻¹ * m) * negVal nu y J m *
        (thetaVal θ y J m⁻¹ * (negVal nu y J ((fst T A ≫ x)⁻¹ * m))⁻¹) := by
  subst hx
  have e₁ : (lift (fst T A) m).left ≫ (translT A θ.pt⁻¹).left = (lift (fst T A) ((fst T A ≫ θ.pt)⁻¹ * m)).left := by
    rw [← Over.comp_left, lift_translT, comp_inv']
  have e₂ : (lift (fst T A) m).left ≫ (negT A T).left = (lift (fst T A) m⁻¹).left := by
    rw [← Over.comp_left, lift_negT]
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_pull hJ _ _ _).trans ?_) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans ?_))))))
  · rw [e₁]; rfl
  · rw [e₂]; rfl
  · rw [e₁]; rfl
end GlobalTheory.SymLiftOdd
