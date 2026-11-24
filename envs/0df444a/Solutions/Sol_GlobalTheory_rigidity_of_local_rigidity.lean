-- Prove2me | solution 1 for GlobalTheory.rigidity_of_local_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:42.127115+00:00
-- url     : https://prove2.me/submissions/129731ec-638e-499a-86d1-9300fcb1f7a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Theorems.Thm_GlobalTheory_eq_comp_section_of_local_rigidity
import Theorems.Thm_GlobalTheory_surjective_app_of_isAbelianScheme
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → RigiditySt := by
  intro hG hR S A B _ _ hA hB f hf
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := hB.proper
  let g : A ⊗ A ⟶ B := (fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)
  let ε : A ⟶ A ⊗ A := lift 1 (𝟙 A)
  let j : A ⟶ A ⊗ A := lift (𝟙 A) 1
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf, Hom.one_def]
  have hε : ε ≫ g = f := by
    simp only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      inv_one, _root_.one_mul, Category.id_comp]
  have hj : j ≫ g = 1 := by
    simp only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
      _root_.mul_one, inv_mul_cancel]
  have hεp : ε.left ≫ (snd A A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd A A).left := by
    change Smooth (pullback.snd A.hom A.hom); infer_instance
  have huc : UniversallyClosed (snd A A).left := by
    change UniversallyClosed (pullback.snd A.hom A.hom); infer_instance
  have hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left := by
    have hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom := .of_hasPullback A.hom A.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst A A).left = 𝟙 A.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hη]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]
      rfl
  have key : g.left = (snd A A).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp
      ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap
      (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_
    intro s
    refine ⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hη]; rfl
    · intro x hx
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left,
        Scheme.Hom.comp_apply]
      rfl
  have key' : g = snd A A ≫ f := by
    rw [← hε]
    exact Over.OverMorphism.ext key
  have hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f) := by
    rw [← key', mul_inv_cancel_left]
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  rw [hmul]
  congr 1
end GlobalTheory
