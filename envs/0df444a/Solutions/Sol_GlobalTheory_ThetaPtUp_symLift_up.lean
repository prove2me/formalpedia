-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.symLift_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:36.527871+00:00
-- url     : https://prove2.me/submissions/f84f8d76-5b27-4763-98fa-3f86f9cd8511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_P2M_GlobalTheory_ThetaPtUp_exists_psi_inv__3417de49043e
import Theorems.Thm_GlobalTheory_ThetaPtUp_exists_genThrough_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_isTwistPull_up
import Theorems.Thm_GlobalTheory_GlobalLift_val_powGen
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_ThetaAct_translPt_one
import Theorems.Thm_GlobalTheory_ThetaAct_translT_snd
import Theorems.Thm_GlobalTheory_ThetaAct_translT_translPt
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_inv
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_pow
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_lift
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_neg
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_tr__fb963db54922
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaPtUp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ] (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtUp
theorem _root_.solution [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ : ThetaGrp A L₁ k T}
    (H₁ : SymLift A L₁ k n x θ) : ∃ θ₀ : ThetaGrp G L₀ k T₀, SymLift G L₀ k n x₀ θ₀ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf A L₁ k θ s s' →
        IsActOf G L₀ k θ₀ s₀ s₀' := by
  obtain ⟨rfl, hpow, ν, hν, hs⟩ := H₁
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨a, ha, v⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_tr' hp τ hτ _ x₀ hx) θ.φ θ.isGen
  obtain ⟨ν₀, hν₀, u⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_neg hp τ hτ) ν hν
  let θ₀ : ThetaGrp G L₀ k T₀ := ⟨x₀, a, ha⟩
  have t : ∀ {y : T ⟶ A} {y₀ : T₀ ⟶ G}, τ ≫ y₀.left = y.left ≫ φ →
      (χ ≫ psi hp τ hτ) ≫ (translT G y₀).left = (χ ≫ (translT A y).left) ≫ psi hp τ hτ :=
    fun h => by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_transl hp τ hτ _ _ h).symm
  have t₁ : ∀ y : T ⟶ A, (χ ≫ (translT A y).left) ≫ (snd T A).left = χ ≫ (translPt A y).left := fun y => by
    rw [Category.assoc, ThetaAct.translT_snd]
  have t₂ : ∀ y : T ⟶ A, (χ ≫ (translT A y).left) ≫ (translPt A θ.pt).left = χ ≫ (translPt A (θ.pt * y)).left :=
    fun y => by rw [Category.assoc, ← Over.comp_left, ThetaAct.translT_translPt]
  refine ⟨θ₀, ⟨rfl, corr_of_val hL₀ fun y J hJ => ?_, ν₀, hν₀, corr_of_val hL₀ fun y J hJ => ?_⟩,
    fun s₀ s₀' s s' h h' H => isTwistPull_up hp τ hτ hL₀ hL₁ (psi_tr' hp τ hτ _ x₀ hx) ha v h h' H⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := val_corr hJ' hpow χ
    rw [val_powGen _ _ _ hJ', val_one] at q
    rw [val_powGen _ _ _ hJ, val_one, ← h₂]
    let F : ℕ → ((T₀ ⊗ G).left.presheaf.stalk y)ˣ := fun i => wVal w y J J' (χ ≫ (translPt A (θ.pt ^ i)).left) ^ k
    have e : ∀ i : ℕ, tval θ₀ ((χ ≫ psi hp τ hτ) ≫ (translT G (θ₀.pt ^ i)).left) y J =
        F i / F (i + 1) * tval θ (χ ≫ (translT A (θ.pt ^ i)).left) y J' := fun i => by
      rw [t (over_pow hp τ hτ hx i)]
      refine (v _ _ _ _ _ hJ hJ').trans ?_
      rw [t₁, t₂, ← pow_succ', zpow_neg, div_eq_mul_inv]
      rfl
    have e₀ : ∏ i : Fin n, F i / F (i + 1) = 1 := by
      rw [Fin.prod_univ_eq_prod_range (fun i => F i / F (i + 1)), Finset.prod_range_div', div_eq_one]
      simp only [F, hn, pow_zero]
    simp only [e, Finset.prod_mul_distrib, e₀, _root_.one_mul]
    exact q
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := val_corr hJ' hs χ
    rw [val_symGen _ _ _ hJ', val_one] at q
    refine (val_symGen θ₀ ν₀ _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    have n₀ : (χ ≫ psi hp τ hτ) ≫ (negT G T₀).left = (χ ≫ (negT A T).left) ≫ psi hp τ hτ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_lift hp τ hτ (psi_neg hp τ hτ)).symm
    have n₁ : (χ ≫ (negT A T).left) ≫ (snd T A).left = χ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [Category.assoc, ← Over.comp_left, negT, lift_snd]
    have n₂ : (χ ≫ (translT A θ.pt⁻¹).left) ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left =
        (χ ≫ (negT A T).left) ≫ (translPt A θ.pt).left := by
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left]
      congr 2
      show translT A θ.pt⁻¹ ≫ (snd T A)⁻¹ = negT A T ≫ ((fst T A ≫ θ.pt) * snd T A)
      rw [GrpObj.comp_inv, MonObj.comp_mul, translT, negT, lift_snd, lift_snd, lift_fst_assoc]
      show ((fst T A ≫ θ.pt⁻¹) * snd T A)⁻¹ = (fst T A ≫ θ.pt) * (snd T A)⁻¹
      rw [mul_inv, GrpObj.comp_inv, inv_inv]
    have n₃ : χ ≫ (translPt A (θ.pt * θ.pt⁻¹)).left = χ ≫ (snd T A).left := by
      rw [mul_inv_cancel, ThetaAct.translPt_one]
    rw [← h₂, t (over_inv hp τ hτ hx), n₀]
    have a₁ := v _ (χ ≫ (translT A θ.pt⁻¹).left) y J J' hJ hJ'
    have a₂ := u _ χ y J J' hJ hJ'
    have a₃ := v _ (χ ≫ (negT A T).left) y J J' hJ hJ'
    have a₄ := u _ (χ ≫ (translT A θ.pt⁻¹).left) y J J' hJ hJ'
    rw [t₂, n₃] at a₁
    rw [n₁] at a₃
    rw [n₂] at a₄
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) a₁ a₂) (congrArg₂ (fun p q => p * q⁻¹) a₃ a₄)).trans
      (Eq.trans ?_ q)
    have key : ∀ {U : Type} [CommGroup U] (p₁ p₂ p₃ p₄ a b c d : U),
        (p₁ * p₂⁻¹ * a * (p₂ * p₃⁻¹ * b)) * (p₃ * p₄⁻¹ * c * (p₁ * p₄⁻¹ * d)⁻¹) = (a * b) * (c * d⁻¹) :=
      fun p₁ p₂ p₃ p₄ a b c d => by
        apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    simp only [zpow_neg]
    exact key _ _ _ _ _ _ _ _
end GlobalTheory.ThetaPtUp
