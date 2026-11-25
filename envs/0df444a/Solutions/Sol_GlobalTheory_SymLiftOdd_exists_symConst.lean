-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.exists_symConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:06.68928+00:00
-- url     : https://prove2.me/submissions/95c17a88-7673-4933-88ae-21ad35fd7ebd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_constT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translPt
import Theorems.Thm_GlobalTheory_SymLiftOdd_translT_eq
import Theorems.Thm_GlobalTheory_SymLiftOdd_negT_eq
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_inv__c2958fec9ffd
import Theorems.Thm_GlobalTheory_SymLiftOdd_symGen_isGen

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
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (θ : ThetaGrp A L k T)
    {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val (symGen A L k θ nu) (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  have := hA.comm
  refine exists_constT hG hA hL (fun U _ h => ?_) (symGen_isGen θ hnu)
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← Over.comp_left]
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [e, translT_eq, negT_eq, comp_inv', comp_inv', lift_snd, lift_snd, lift_translPt, lift_translPt,
    mul_inv_cancel_left, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module
end GlobalTheory.SymLiftOdd
