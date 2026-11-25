-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.symLift_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:41:05.886461+00:00
-- url     : https://prove2.me/submissions/15d9b8a2-40a2-4230-b455-2feee5dacd58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_tr__fb963db54922
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_pow
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_inv
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_lift
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_neg
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_exists_genThrough__63f4702df31d
import Theorems.Thm_GlobalTheory_ThetaPtMove_isTwistPull_move
import Theorems.Thm_GlobalTheory_GlobalLift_val_powGen
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_ThetaAct_translPt_one
import Theorems.Thm_GlobalTheory_ThetaAct_translT_snd
import Theorems.Thm_GlobalTheory_ThetaAct_translT_translPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_transl


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) : ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf G L₀ k θ₀ s₀ s₀' →
        IsActOf A L₁ k θ s s' := by
  obtain ⟨rfl, hpow, ν₀, hν₀, hs⟩ := H₀
  obtain ⟨a, ha, v⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_tr' hp τ hτ x _ hx) θ₀.φ θ₀.isGen
  obtain ⟨ν, hν, u⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_neg hp τ hτ) ν₀ hν₀
  let θ : ThetaGrp A L₁ k T := ⟨x, a, ha⟩
  have t : ∀ {y : T ⟶ A} {y₀ : T₀ ⟶ G}, τ ≫ y₀.left = y.left ≫ φ →
      (𝟙 _ ≫ psi hp τ hτ) ≫ (translT G y₀).left = (𝟙 _ ≫ (translT A y).left) ≫ psi hp τ hτ :=
    fun h => by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_transl hp τ hτ _ _ h).symm
  have t₁ : ∀ y : T ⟶ A, (𝟙 _ ≫ (translT A y).left) ≫ (snd T A).left = (translPt A y).left := fun y => by
    rw [Category.id_comp, ThetaAct.translT_snd]
  have t₂ : ∀ y : T ⟶ A, (𝟙 _ ≫ (translT A y).left) ≫ (translPt A x).left = (translPt A (x * y)).left := fun y => by
    rw [Category.id_comp, ← Over.comp_left, ThetaAct.translT_translPt]
  refine ⟨θ, ⟨rfl, corr_of_val hL₁ fun y J' hJ' => ?_, ν, hν, corr_of_val hL₁ fun y J' hJ' => ?_⟩,
    fun s₀ s₀' s s' h h' H => isTwistPull_move hp τ hτ hL₀ hL₁ (psi_tr' hp τ hτ x _ hx) ha v h h' H⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := val_corr hJ hpow (𝟙 _ ≫ psi hp τ hτ)
    rw [val_powGen _ _ _ hJ, val_one] at q
    rw [val_powGen _ _ _ hJ', val_one]
    let F : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ := fun i => wVal w y J J' (translPt A (x ^ i)).left ^ k
    have e : ∀ i : ℕ, tval θ₀ ((𝟙 _ ≫ psi hp τ hτ) ≫ (translT G (θ₀.pt ^ i)).left) y J =
        F i / F (i + 1) * tval θ (𝟙 _ ≫ (translT A (x ^ i)).left) y J' := fun i => by
      rw [t (over_pow hp τ hτ hx i)]
      refine (v _ _ _ _ _ hJ hJ').trans ?_
      rw [t₁, t₂, ← pow_succ', zpow_neg, div_eq_mul_inv]
      rfl
    have e₀ : ∏ i : Fin n, F i / F (i + 1) = 1 := by
      rw [Fin.prod_univ_eq_prod_range (fun i => F i / F (i + 1)), Finset.prod_range_div', div_eq_one]
      simp only [F, hn, pow_zero]
    simp only [e, Finset.prod_mul_distrib, e₀, _root_.one_mul] at q
    exact q
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := val_corr hJ hs (𝟙 _ ≫ psi hp τ hτ)
    rw [val_symGen _ _ _ hJ, val_one] at q
    refine (val_symGen θ ν _ hJ').trans (Eq.trans ?_ (val_one _).symm)
    have n₀ : (𝟙 _ ≫ psi hp τ hτ) ≫ (negT G T₀).left = (𝟙 _ ≫ (negT A T).left) ≫ psi hp τ hτ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_lift hp τ hτ (psi_neg hp τ hτ)).symm
    have n₁ : (𝟙 _ ≫ (negT A T).left) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [Category.assoc, ← Over.comp_left, negT, lift_snd]
    have n₂ : (𝟙 _ ≫ (translT A x⁻¹).left) ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left =
        (𝟙 _ ≫ (negT A T).left) ≫ (translPt A x).left := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left]
      congr 1
      show translT A x⁻¹ ≫ (snd T A)⁻¹ = negT A T ≫ ((fst T A ≫ x) * snd T A)
      rw [GrpObj.comp_inv, MonObj.comp_mul, translT, negT, lift_snd, lift_snd, lift_fst_assoc]
      show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = (fst T A ≫ x) * (snd T A)⁻¹
      rw [mul_inv, GrpObj.comp_inv, inv_inv]
    have n₃ : (translPt A (x * x⁻¹)).left = 𝟙 _ ≫ (snd T A).left := by
      rw [mul_inv_cancel, ThetaAct.translPt_one, Category.id_comp]
    rw [t (over_inv hp τ hτ hx), n₀] at q
    have a₁ := v _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    have a₂ := u _ (𝟙 _) y J J' hJ hJ'
    have a₃ := v _ (𝟙 _ ≫ (negT A T).left) y J J' hJ hJ'
    have a₄ := u _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    rw [t₂, n₃] at a₁
    rw [n₁] at a₃
    rw [n₂] at a₄
    have q' := (congrArg₂ (· * ·) (congrArg₂ (· * ·) a₁ a₂) (congrArg₂ (fun p q => p * q⁻¹) a₃ a₄)).symm.trans q
    refine Eq.trans ?_ q'
    have key : ∀ {U : Type} [CommGroup U] (p₁ p₂ p₃ p₄ a b c d : U), (a * b) * (c * d⁻¹) =
        (p₁ * p₂⁻¹ * a * (p₂ * p₃⁻¹ * b)) * (p₃ * p₄⁻¹ * c * (p₁ * p₄⁻¹ * d)⁻¹) := fun p₁ p₂ p₃ p₄ a b c d => by
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    simp only [zpow_neg]
    exact key _ _ _ _ _ _ _ _
end GlobalTheory.ThetaPtMove
