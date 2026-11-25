-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:05.167579+00:00
-- url     : https://prove2.me/submissions/d71dcd80-adbb-4224-8452-3887da2b618d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactor
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_mp_box_tmul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hU : USt F) (f : Z1 (box F))
    (hf : ∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) :
    ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by

  have hk : ∀ {b b' : C} (ψ : b ⟶ b') {a a' : C} (φ : a ⟶ a'),
      f.1 (a', b) (a', b') (𝟙 a', ψ) =
        mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
          (f.1 (a, b) (a, b') (𝟙 a, ψ)) := by
    intro b b' ψ a a' φ
    have e1 := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ, 𝟙 b) (𝟙 a', ψ)
    have e2 := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a', b'))
      (𝟙 a, ψ) (φ, 𝟙 b')
    have e : (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ)) =
        (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) := by
      simp
    rw [e, e2, hf a a' b' φ, add_zero, hf a a' b φ, map_zero, zero_add] at e1
    exact e1.symm
  have hcomm : ∀ {a a' b' : C} (φ : a ⟶ a') (x : F.obj a ⊗[R] F.obj b'),
      TensorProduct.comm R (F.obj a') (F.obj b')
          (mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) x) =
        (mp F φ).toLinearMap.lTensor (F.obj b') (TensorProduct.comm R (F.obj a) (F.obj b') x) := by
    intro a a' b' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rw [mp_box_tmul, mp_id]; simp
    | add u v hu hv => simp only [map_add, hu, hv]

  have hex : ∀ {b b' : C} (ψ : b ⟶ b'), ∃! m : F.obj b', ∀ a : C,
      f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m := by
    intro b b' ψ
    obtain ⟨m, hm, hu⟩ := hU (F.obj b')
      (fun a ↦ TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)))
      (fun a a' φ ↦ by rw [hk ψ φ, hcomm])
    have hiff : ∀ (a : C) (m' : F.obj b'),
        TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)) = m' ⊗ₜ[R] (1 : F.obj a) ↔
          f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m' := by
      intro a m'
      exact (TensorProduct.comm R (F.obj a) (F.obj b')).injective.eq_iff' (TensorProduct.comm_tmul R _ _ _ _)
    exact ⟨m, fun a ↦ (hiff a m).1 (hm a), fun m' h ↦ hu m' fun a ↦ (hiff a m').2 (h a)⟩
  choose y hy huniq using @hex
  refine ⟨⟨fun b b' ψ ↦ y ψ, fun b b' b'' ψ χ ↦ ?_⟩, ?_⟩
  · refine (huniq (ψ ≫ χ) _ fun a ↦ ?_).symm
    have e := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a, b''))
      (𝟙 a, ψ) (𝟙 a, χ)
    have e' : (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a, b'') from (𝟙 a, χ)) = (𝟙 a, ψ ≫ χ) := by
      simp
    rw [e', hy ψ a, hy χ a] at e
    refine e.trans ?_
    rw [mp_box_tmul, mp_id, TensorProduct.tmul_add]
  · refine Subtype.ext ?_
    funext T T' φ
    obtain ⟨a, b⟩ := T
    obtain ⟨a', b'⟩ := T'
    obtain ⟨φ₁, φ₂⟩ := φ
    have e := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ₁, 𝟙 b) (𝟙 a', φ₂)
    have e' : (show ((a, b) : C × C) ⟶ (a', b) from (φ₁, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', φ₂)) = (φ₁, φ₂) := by
      simp
    rw [e', hf a a' b φ₁, map_zero, zero_add, hy φ₂ a'] at e
    exact e.symm
end GlobalTheory.CompanionTheory.Axis
