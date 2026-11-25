-- Prove2me | solution 1 for GlobalTheory.PsiScalUnit.cub_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:15.322377+00:00
-- url     : https://prove2.me/submissions/1bfac798-8f8f-41f9-bed4-07d0d92d6aab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiScalarsRelationsUpToBaseUnits
import Theorems.Thm_GlobalTheory_PsiScalUnit_exists_ratio
import Theorems.Thm_GlobalTheory_PsiScalUnit_ev_unit
import Theorems.Thm_GlobalTheory_PsiScalUnit_c_left
import Theorems.Thm_GlobalTheory_PsiScalUnit_exists_setup
import Theorems.Thm_GlobalTheory_PsiScalUnit_ev_inj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.PsiScalUnit
variable {V : Type} [CommRing V] [IsDomain V]
namespace GlobalTheory.PsiScalUnit
theorem _root_.solution (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hB : D.TauBimult) (x y w : D.X) :
    ∃ u : Vˣ, (a (x + y + w) * a x * a y * a w).val =
      algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + w) * a (y + w)).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK V)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 x y w)) (𝟙 _) z J =
      cubV D.cub z J (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w) := by
    refine (val_cub D.cub (𝟙 (TK V)) hJ (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w)).trans ?_
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB x y w) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [vc, vτ, vτ, vτ, vρ] at e
  simp only [hψ] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have p₁ := prod_cub (DVR.cP D (𝟙_ _) x) (DVR.cP D _ y) (DVR.cP D _ w) f
      have q : eSec D.P.A = (1 : 𝟙_ _ ⟶ D.P.A).left := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
      refine Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ rfl p₁).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c_left, DVR.cPoint_add, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y)).1 (h (x + w)).1) (h (y + w)).1)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y + w)).1 (h x).1) (h y).1) (h w).1)
      D.rig_gen) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε _ D.cub.isGen
        (lift (DVR.cP D (𝟙_ _) x) (lift (DVR.cP D (𝟙_ _) y) (DVR.cP D (𝟙_ _) w))).left))
  have e₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)).symm.trans
    ((hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) rfl)) rfl))
      (val_cub D.cub (toUnit (TK V)) hJ _ _ _)))))
  rw [DVR.comp_cP, DVR.comp_cP, DVR.comp_cP] at e₂
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (x + y + w) * a x * a y * a w) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a (x + y) * a (x + w) * a (y + w)) := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this
end GlobalTheory.PsiScalUnit
