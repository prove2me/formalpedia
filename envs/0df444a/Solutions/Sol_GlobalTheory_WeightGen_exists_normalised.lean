-- Prove2me | solution 1 for GlobalTheory.WeightGen.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:03.688277+00:00
-- url     : https://prove2.me/submissions/1437a8c5-9bd2-44fa-b47e-ec3f68380930

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_exists_gen
import Theorems.Thm_GlobalTheory_WeightGen_gen_unique_of_invariant
import Theorems.Thm_P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
import Theorems.Thm_P2M_GlobalTheory_WeightGen_prod_O__b03d1f1ebbf3
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.WeightGen
theorem _root_.solution {T S₀ P : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (π : T ⟶ S₀)
    (e : S₀ ⟶ T) (he : e ≫ π = 𝟙 _) (heq : e ≫ q = 1) (a p : P ⟶ T) (hq : a ≫ q = p ≫ q)
    (hπ : a ≫ π = p ≫ π)
    (hp : ∀ f : Γ(T.left, ⊤), a.left.appTop.hom f = p.left.appTop.hom f →
      ∃ c, π.left.appTop.hom c = f)
    (c : D.X → GermFn P.left)
    (hc : ∀ χ χ' Z r z, c (χ + χ') Z r z = c χ Z r z * c χ' Z r z)
    (H : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val t (r ≫ a.left) z J = c χ Z r z * val t (r ≫ p.left) z J) :
    ∃ t : ∀ χ, LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), (∀ χ, (t χ).IsGen) ∧
      (∀ χ χ', LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
            (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left))
        (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) ∧
      (∀ χ y J, Good D.P.L y J → val (t χ) e.left y J = 1) ∧
      ∀ χ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val (t χ) (r ≫ a.left) z J = c χ Z r z * val (t χ) (r ≫ p.left) z J := by
  choose t₀ g₀ w₀ using H
  have hL := D.P.isLB
  have norm : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (t₀ χ) r z J * (val (t₀ χ) (r ≫ (π ≫ e).left) z J)⁻¹ := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
        have z : (π ≫ e) ≫ q = 1 := by rw [Category.assoc, heq, MonObj.comp_one]
        have := prod_Oφ D ((π ≫ e) ≫ q) χ h
        refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ k, h (D.Oφ q χ k) ^ Oinvε k) rfl (DVR.prod_neg _ _
            ((Finset.prod_congr rfl fun k _ =>
              congrArg (fun g => h g ^ Oinvε k) (comp_Oφ D (π ≫ e) q χ k)).trans this))) ?_
        rw [z, _root_.one_mul]
        simp)
      (LB.mulGen D.P.L _ _ _ _ (t₀ χ) (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (t₀ χ) (π ≫ e).left)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g₀ χ) (DVR.invGen_isGen _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ (g₀ χ) _)))
    exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩
  choose t g v using norm
  have unit : ∀ χ y J, Good D.P.L y J → val (t χ) e.left y J = 1 := fun χ y J hJ => by
    rw [v χ _ _ y J hJ, ← Over.comp_left, reassoc_of% he, mul_inv_cancel]
  have wgt : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
      val (t χ) (r ≫ a.left) z J = c χ Z r z * val (t χ) (r ≫ p.left) z J := fun χ Z r z J hJ => by
    have k : a.left ≫ (π ≫ e).left = p.left ≫ (π ≫ e).left :=
      congrArg (fun g => g.left) (show a ≫ π ≫ e = p ≫ π ≫ e by rw [reassoc_of% hπ])
    rw [v χ _ _ z J hJ, v χ _ _ z J hJ, w₀ χ Z r z J hJ, Category.assoc, Category.assoc, k, _root_.mul_assoc]
  refine ⟨t, g, fun χ χ' => corr_of_val hL fun y J hJ => ?_, unit, wgt⟩
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {z : T'.left} {J},
      Good D.P.L z J → val (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
            (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left)) ρ.left z J =
        val (t (χ + χ')) ρ.left z J *
          cubV D.cub z J (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (ρ ≫ q) := fun ρ z J hJ => by
    refine (val_mul hJ _ _ _).trans (congrArg _ ((val_cub D.cub ρ hJ _ _ _).trans ?_))
    rw [comp_toUnit_assoc, comp_toUnit_assoc]
  refine gen_unique_of_invariant hL (u := LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
        (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left)) (fun U _ h => ?_) π.left e.left
    (congrArg (fun g => g.left) he) a.left p.left hp
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g _) (g _)) (fun y J hJ => ?_) (fun y J hJ => ?_) _ _ y J hJ
  · refine (DVR.prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_Oφ D q (χ + χ') h)
      (prod_cub _ _ _ h)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
        (prod_Oφ D q χ h) (prod_Oφ D q χ' h)).symm)
    have e₁ : toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
      rw [D.c_add]; exact MonObj.comp_mul _ _ _
    rw [e₁, mul_comm q, mul_comm q, mul_comm q]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [ev e hJ, val_mul hJ, unit _ y J hJ, unit _ y J hJ, unit _ y J hJ, heq,
      (isCub_cubV D.cub hJ).face₃]
  · have w := fun χ => wgt χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at w
    rw [ev a hJ, ev p hJ, val_mul hJ, val_mul hJ, w, w, w, hc, hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.WeightGen
