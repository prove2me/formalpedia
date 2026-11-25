-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.symLift_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:38.009844+00:00
-- url     : https://prove2.me/submissions/a7644199-4908-4483-956a-327216d9a63c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_powGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_ratio
import Theorems.Thm_GlobalTheory_SymLiftOdd_id_eq_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    (θ θ' : ThetaGrp A L k T) (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ') :
    LB.Gen.Corr L _ _ _ _ θ.φ θ'.φ := by
  obtain ⟨p, φ, hφ⟩ := θ
  obtain ⟨p', φ', hφ'⟩ := θ'
  obtain rfl : p = x := h.pt_eq
  obtain rfl : p' = p := h'.pt_eq
  obtain ⟨nu, hnu, hs⟩ := h.sym
  obtain ⟨nu', hnu', hs'⟩ := h'.sym
  obtain ⟨c, hc⟩ := exists_ratio hG hA hL hφ hφ'
  obtain ⟨d, hd⟩ := exists_ratio hG hA hL hnu hnu'
  refine corr_of_val hL fun y J hJ => ?_
  have hc' : ∀ m, thetaVal ⟨p', φ, hφ⟩ y J m = thetaVal ⟨p', φ', hφ'⟩ y J m * gm (fst T A).left y ⊤ c :=
    fun m => hc m y J hJ
  have hd' : ∀ m, negVal nu y J m = negVal nu' y J m * gm (fst T A).left y ⊤ d := fun m => hd m y J hJ
  have s₁ := (val_symGen _ nu rfl hJ (snd T A)).symm.trans ((val_corr hJ hs _).trans (val_one _))
  have s₂ := (val_symGen _ nu' rfl hJ (snd T A)).symm.trans ((val_corr hJ hs' _).trans (val_one _))
  have q₁ := (val_powGen _ n rfl hJ (snd T A)).symm.trans ((val_corr hJ h.pow_eq _).trans (val_one _))
  have q₂ := (val_powGen _ n rfl hJ (snd T A)).symm.trans ((val_corr hJ h'.pow_eq _).trans (val_one _))
  rw [Finset.prod_congr rfl fun j _ => hc' _, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at q₁
  rw [hc', hc', hd', hd'] at s₁
  have c2 : gm (fst T A).left y ⊤ c ^ 2 = 1 := by
    apply Additive.ofMul.injective
    replace s₁ := congrArg Additive.ofMul s₁
    replace s₂ := congrArg Additive.ofMul s₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at s₁ s₂ ⊢
    linear_combination (norm := module) s₁ - s₂
  have cn : gm (fst T A).left y ⊤ c ^ n = 1 := (_root_.one_mul _).symm.trans ((congrArg (· * _) q₂.symm).trans q₁)
  obtain ⟨l, rfl⟩ := hn
  rw [pow_succ, pow_mul, c2, one_pow, _root_.one_mul] at cn
  have := hc (snd T A) y J hJ
  rw [cn, _root_.mul_one, ← id_eq_lift] at this
  exact this
end GlobalTheory.SymLiftOdd
