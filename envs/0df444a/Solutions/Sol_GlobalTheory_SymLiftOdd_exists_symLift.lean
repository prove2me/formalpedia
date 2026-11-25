-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.exists_symLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:00.279792+00:00
-- url     : https://prove2.me/submissions/e965bffe-3f3e-47a9-9162-562347176d5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_defect_pow
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_constT
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_powGen_isGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_powGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_form_pow
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_symConst
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_scale
import Theorems.Thm_GlobalTheory_SymLiftOdd_id_eq_lift
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
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    (hx : x ^ n = 1) (θ : ThetaGrp A L k T) (hθ : θ.pt = x) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ θ' : ThetaGrp A L k T, SymLift A L k n x θ' := by
  have := hA.comm
  obtain ⟨a, ha⟩ := exists_symConst hG hA hL θ hnu
  obtain ⟨b, hb⟩ := exists_constT hG hA hL (form_pow (k := k) (hθ ▸ hx : θ.pt ^ n = 1)) (powGen_isGen θ n)
  have hab : ∀ y J, Good L y J → gm (fst T A).left y ⊤ a ^ n = gm (fst T A).left y ⊤ b ^ 2 := fun y J hJ =>
    defect_pow (thetaVal θ y J) (negVal nu y J) (fst T A ≫ x) n (by rw [← comp_pow', hx, MonObj.comp_one]) _ _
      (fun m => (val_symGen θ nu hθ hJ m).symm.trans (ha m y J hJ)) (by
        rw [← hb 1 y J hJ, val_powGen θ n hθ hJ]; simp only [_root_.mul_one])
  obtain ⟨l, rfl⟩ := hn
  obtain ⟨θ', hpt, hv⟩ := exists_scale hL θ (b⁻¹ * a ^ l)
  have hθ' : θ'.pt = x := hpt.trans hθ
  refine ⟨θ', hθ', corr_of_val hL fun y J hJ => ?_, nu, hnu, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_one, id_eq_lift, val_powGen θ' _ hθ' hJ, Finset.prod_congr rfl fun j _ => hv y J hJ _,
      Finset.prod_mul_distrib, ← val_powGen θ _ hθ hJ, hb _ y J hJ, Finset.prod_const, Finset.card_range, map_mul,
      map_inv, map_pow, mul_pow, ← pow_mul, mul_comm l, pow_mul, hab y J hJ]
    generalize gm (fst T A).left y ⊤ b = β
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one]
    module
  · have e₁ := (val_symGen θ nu hθ hJ (snd T A)).symm.trans (ha _ y J hJ)
    have e₂ := hab y J hJ
    rw [val_one, id_eq_lift, val_symGen θ' nu hθ' hJ, hv y J hJ, hv y J hJ, map_mul, map_inv, map_pow]
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    replace e₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
    linear_combination (norm := module) e₁ + e₂
end GlobalTheory.SymLiftOdd
