-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_biTriv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:43.667866+00:00
-- url     : https://prove2.me/submissions/f60412e8-9899-45b9-b9d9-9bad4c20d8c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_GlobalTheory_UU_PackageDescent_prod_lam
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution [IsCommMonObj H] [IsMonHom i] {P : CP G} (s : BiTriv P.c i) :
    ∃ s' : BiTriv P.c i, ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
      val s'.s (lift t x).left z J = val s.s (lift t⁻¹ x⁻¹).left z J * val P.sym (t ≫ i).left z J *
        val P.sym x.left z J * (val P.sym ((t ≫ i) * x).left z J)⁻¹ := by
  let sy := fun p : H ⊗ G ⟶ G => LB.pullGen P.L.L _ _ P.sym p.left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ P.sym_gen _
  obtain ⟨a, ha, va⟩ := exists_gen P.L.isLB (φ' := lamφ i) (ε' := Oε)
    (fun U _ h => by
      refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 2) (K' := Fin 2) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (prod_lam (fst H G)⁻¹ (snd H G)⁻¹ h)
            (prod_sym (fst H G ≫ i) h)) (prod_sym (snd H G) h))
          (c' := (h (((fst H G ≫ i) * snd H G)⁻¹).left * (h ((fst H G ≫ i) * snd H G).left)⁻¹)⁻¹) ?_).trans ?_
      · rw [← prod_sym, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun k _ => zpow_neg _ _
      · have e := prod_lam (i := i) (fst H G) (snd H G) h
        rw [lift_fst_snd, Over.id_left] at e
        simp only [Category.id_comp] at e
        rw [e, GrpObj.inv_comp, ← mul_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
    (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _
      (LB.pullGen P.L.L _ _ s.s (lift (fst H G)⁻¹ (snd H G)⁻¹).left) (sy (fst H G ≫ i))) (sy (snd H G)))
      (LB.invGen P.L.L _ _ (sy ((fst H G ≫ i) * snd H G))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ s.gen _) (gs _)) (gs _)) (DVR.invGen_isGen _ _ _ _ (gs _)))
  have v : ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
      val a (lift t x).left z J = val s.s (lift t⁻¹ x⁻¹).left z J * val P.sym (t ≫ i).left z J *
        val P.sym x.left z J * (val P.sym ((t ≫ i) * x).left z J)⁻¹ := by
    intro T t x z J hJ
    rw [va _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc]
  refine ⟨⟨a, ha, fun T t t' x z J hJ => ?_, fun T t x x' z J hJ => ?_⟩, v⟩
  · have e := P.sym_cub T (t ≫ i) (t' ≫ i) x z J hJ
    rw [v _ _ _ z J hJ, v _ _ _ z J hJ, v _ _ _ z J hJ, mul_inv, s.law1 _ _ _ _ z J hJ, GrpObj.inv_comp,
      GrpObj.inv_comp, MonObj.mul_comp]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := P.sym_cub T (t ≫ i) x x' z J hJ
    rw [v _ _ _ z J hJ, v _ _ _ z J hJ, v _ _ _ z J hJ, mul_inv, s.law2 _ _ _ _ z J hJ, GrpObj.inv_comp,
      ← _root_.mul_assoc (t ≫ i)]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
end GlobalTheory.UU.PackageDescent
