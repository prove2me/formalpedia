-- Prove2me | solution 1 for GlobalTheory.PsiScalUnit.even_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:37.564235+00:00
-- url     : https://prove2.me/submissions/a613ae03-0d6b-4d30-8a25-f4c658e253a0

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hE : D.PsiEven) (x : D.X) :
    ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE x) (𝟙 _))
  rw [hψ, hψ, Category.id_comp] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have q : (D.c x).left ≫ (ι[D.P.A]).left = (D.c (-x)).left := by
        have h0 : DVR.cP D (𝟙_ _) 0 = 1 := by simpa using DVR.cPoint_nsmul D (𝟙_ _) 0 x
        have h1 := DVR.cPoint_add D (𝟙_ _) (-x) x
        rw [neg_add_cancel, h0] at h1
        rw [c_left, c_left, eq_inv_of_mul_eq_one_left h1.symm, ← Over.comp_left]
        rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (h x).1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (-x)).1 (DVR.pullGen_isGen D.P.L _ _ _ D.sym_gen (D.c x).left))
  have e₂ := (hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (-x)) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a x) := by
    have e' : Units.map (ev z).toMonoidHom (a (-x)) * val (ga (-x)) (toUnit (TK V)).left z J *
        val D.sym ((toUnit (TK V)).left ≫ (D.c x).left) z J =
        Units.map (ev z).toMonoidHom (a x) * val (ga x) (toUnit (TK V)).left z J := e
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e'
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this
end GlobalTheory.PsiScalUnit
