-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.eq_id_of_twist_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:18.421913+00:00
-- url     : https://prove2.me/submissions/87e4ea6d-5365-4071-92ff-3211e00d3097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_GlobalTheory_TorsionFixedAut_isGen_of_germs
import Theorems.Thm_GlobalTheory_TorsionFixedAut_eq_id_of_sval
import Theorems.Thm_GlobalTheory_TorsionFixedAut_sval_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (σ : A ⟶ A)
  (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution (hL : L.IsLB) (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n)
    (a : Γ((baseOver S).left, ⊤))
    (hF : ∀ (v : SecM A L n (baseOver S)) (Z : Scheme.{0}) (r : Z ⟶ (baseOver S ⊗ A).left) (z : Z) (J), Good L z J →
      secVal (SecM.toSec A (a • v)) r z J = secVal (SecM.toSec A v) (r ≫ (baseOver S ◁ σ).left) z J *
        ((val c (r ≫ (snd (baseOver S) A).left) z J ^ (n : ℤ))⁻¹).val) : σ = 𝟙 A := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  obtain ⟨i', hi, hi'⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme,
      i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ ∧ (A.hom ⁻¹ᵁ ⊤).ι ≫ i' = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id, A.left.topIso.hom_inv_id⟩
  obtain ⟨g, hg⟩ : ∃ g : A.left ⟶ (baseOver S ⊗ A).left, g ≫ (snd (baseOver S) A).left = 𝟙 _ :=
    ⟨(lift (X := baseOver S) (Over.homMk A.hom (Category.comp_id _)) (𝟙 A)).left, by
      rw [← Over.comp_left, lift_snd, Over.id_left]⟩
  have hgσ : g ≫ (baseOver S ◁ σ).left ≫ (snd (baseOver S) A).left = σ.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left, reassoc_of% hg]
  have sec : ∀ j, ∃ v : SecM A L n (baseOver S), ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver S ⊗ A).left) (z : Z) (J),
      Good L z J → secVal (SecM.toSec A v) r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (baseOver S) A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd (baseOver S) A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        refine (Fintype.prod_sum_type _).trans ?_
        simp only [Sum.elim_inl, Category.assoc, hi, Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Fintype.prod_empty, _root_.mul_one, pow_one, zpow_natCast])
      (pullMulSec (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (baseOver S) A).left ≫ i') (LB.oneGen L) (isGen_of_germs _ fun y j j' _ _ =>
          (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
    refine ⟨SecM.ofSec A s', fun Z r z J hJ => (hs' Z r z J hJ).trans ?_⟩
    refine (sval_pullMulSec _ _ _ _ r z hJ).trans ?_
    rw [val_one, Units.val_one, _root_.mul_one]
  choose v hv using sec
  have key : (A.hom ⁻¹ᵁ ⊤).ι ≫ σ.left ≫ i' = 𝟙 _ := by
    refine eq_id_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ ?_ hcov haff
      fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι, Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
        reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (A.hom ⁻¹ᵁ ⊤).toScheme ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, gs (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (fst (baseOver S) A).left) y ⊤ a *
        (val c (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (snd (baseOver S) A).left) y J ^ (n : ℤ)).val, fun j => ?_⟩
      have h₁ := hF (v j) _ ((A.hom ⁻¹ᵁ ⊤).ι ≫ g) y J hJ
      have e₁ : ((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (snd (baseOver S) A).left ≫ i' = 𝟙 _ := by
        rw [Category.assoc, reassoc_of% hg, hi']
      have e₂ : (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (baseOver S ◁ σ).left) ≫ (snd (baseOver S) A).left ≫ i' =
          (A.hom ⁻¹ᵁ ⊤).ι ≫ σ.left ≫ i' := by
        rw [Category.assoc, Category.assoc, reassoc_of% hgσ]
      rw [sval_smul _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, Units.eq_mul_inv_iff_mul_eq, e₁, e₂] at h₁
      exact h₁.symm.trans (mul_right_comm _ _ _)
  apply Over.OverMorphism.ext
  have := congrArg (fun q => i' ≫ q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, reassoc_of% hi, Category.comp_id, Category.id_comp, Over.id_left] using this
end GlobalTheory.TorsionFixedAut
