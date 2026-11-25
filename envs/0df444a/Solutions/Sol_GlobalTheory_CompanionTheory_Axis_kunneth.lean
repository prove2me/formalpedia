-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.kunneth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:35:36.966707+00:00
-- url     : https://prove2.me/submissions/d1cf2513-a14c-47bb-8035-cb089b3d46d1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSectionsAffineFlatStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamilyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparisonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentationStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundaryStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyOfBaseZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_mp_box_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_box_square
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_TrivAt_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_T_class_zero_cocycle_tensor_coboundary
import Theorems.Thm_GlobalTheory_T_cocycle_on_product_from_second_factor
import Theorems.Thm_GlobalTheory_T_cocycle_tensor_coboundary_class_zero
import Theorems.Thm_GlobalTheory_T_flat_cocycle_tensor_representation
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (hf : ∀ T, Module.Flat R (F.obj T)) (hU : USt F) (c : H1 (box F)) :
    ∃ x y : H1 F, c = (boxL F).pull1 x + (boxR F).pull1 y := by
  classical
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hz : ∀ b : C, ∃ t : Z1 F ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ t = f.1 (T, b) (T', b) (φ, 𝟙 b) := fun b ↦ by
    haveI := hf b
    let f₀ : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] F.obj b := fun T T' φ ↦ f.1 (T, b) (T', b) (φ, 𝟙 b)
    refine GlobalTheory.T.flat_cocycle_tensor_representation R C F (F.obj b) f₀ ?_
    intro T T' T'' φ ψ
    have e := Z1.comp f (show ((T, b) : C × C) ⟶ (T', b) from (φ, 𝟙 b)) (show ((T', b) : C × C) ⟶ (T'', b) from (ψ, 𝟙 b))
    rw [mp_box_left] at e
    rw [← e]
    congr 1
    simp
    rfl
  choose t ht using hz
  have hcomp : ∀ (b b' : C) (ψ : b ⟶ b'), (H1.mk F).rTensor _ (t b') =
      (mp F ψ).toLinearMap.lTensor (H1 F) ((H1.mk F).rTensor _ (t b)) := fun b b' ψ ↦ by
    haveI := hf b'
    have k := GlobalTheory.T.cocycle_tensor_coboundary_class_zero R C F (F.obj b') (t b' - (mp F ψ).toLinearMap.lTensor (Z1 F) (t b))
      (fun a ↦ f.1 (a, b) (a, b') (𝟙 a, ψ)) (fun T T' φ ↦ by
        have e : (evZ F φ).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
            (mp F ψ).toLinearMap.lTensor _ ((evZ F φ).rTensor _ (t b)) := by
          rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
            LinearMap.lTensor_comp_rTensor]
        have s := box_square f φ ψ
        rw [map_sub, e, ht, ht]
        exact sub_eq_sub_iff_add_eq_add.2 (by rw [add_comm, ← s, add_comm]))
    have e : (H1.mk F).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
        (mp F ψ).toLinearMap.lTensor _ ((H1.mk F).rTensor _ (t b)) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [map_sub, e, sub_eq_zero] at k
    exact k
  obtain ⟨x, hx, -⟩ := hU (H1 F) (fun b ↦ (H1.mk F).rTensor _ (t b)) hcomp
  obtain ⟨z, rfl⟩ := H1.mk_surjective F x
  have hg : ∀ b : C, ∃ g : ∀ T : C, F.obj T ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ (z ⊗ₜ[R] (1 : F.obj b) - t b) = g T' - (mp F φ).toLinearMap.rTensor _ (g T) := fun b ↦
    GlobalTheory.T.class_zero_cocycle_tensor_coboundary R C F (F.obj b) _ (by
      rw [map_sub, LinearMap.rTensor_tmul, hx b, sub_self])
  choose g hg using hg
  let G : C0 (box F) := fun T ↦ g T.2 T.1
  let f' : Z1 (box F) := f - (boxL F).pullbackOneCocycle z + (d0 (box F)).codRestrict (Z1 (box F)) (commAlgFunctorCoboundaryZero_mem_cocyclesOne _) G
  have hv : ∀ (a a' b : C) (φ : a ⟶ a'), f'.1 (a, b) (a', b) (φ, 𝟙 b) = 0 := fun a a' b φ ↦ by
    have e := hg b a a' φ
    rw [map_sub, LinearMap.rTensor_tmul, ht] at e
    have e2 : mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b)) =
        (mp F φ).toLinearMap.rTensor _ (g b a) := mp_box_left F φ b _
    have e3 : f'.1 (a, b) (a', b) (φ, 𝟙 b) = f.1 (a, b) (a', b) (φ, 𝟙 b) - (z.1 a a' φ) ⊗ₜ[R] (1 : F.obj b) +
        (g b a' - mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b))) := rfl
    rw [e3, e2, ← e]
    change _ - z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) + (z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) - _) = 0
    abel
  obtain ⟨y, hy⟩ := GlobalTheory.T.cocycle_on_product_from_second_factor R C F hU f' hv
  refine ⟨H1.mk F z, H1.mk F y, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add, H1.mk_eq_mk]
  refine ⟨-G, ?_⟩
  rw [hy, map_neg]
  have : (f' : C1 (box F)) = f.1 - ((boxL F).pullbackOneCocycle z).1 + d0 (box F) G := rfl
  change -d0 (box F) G = f.1 - (((boxL F).pullbackOneCocycle z).1 + f'.1)
  rw [this]
  abel
end GlobalTheory.CompanionTheory.Axis
