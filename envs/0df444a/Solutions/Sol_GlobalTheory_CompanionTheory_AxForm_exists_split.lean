-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:00.026425+00:00
-- url     : https://prove2.me/submissions/664a91bf-2fba-4bae-862c-ca297ea53c65

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pt_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pt_id
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (A : Over (Sp R)) [GrpObj A] (y : TT (r1 R B M) ⟶ A ⊗ A)
    (hy : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y = lift (x0 A B) (x0 A B)) :
    ∃ Y : TT (r1 R B (M × M)) ⟶ A ⊗ A,
      pt (ρ := r1 R B (M × M)) (TrivSqZeroExt.fstHom B B (M × M)).toRingHom fst_comp_square_zero_section ≫ Y = lift (x0 A B) (x0 A B) ∧
      pt (mH (LinearMap.fst B M M + LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y = y ∧
      pt (mH (LinearMap.fst B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.fst A A) ≫ lift (𝟙 A) (1 : A ⟶ A) ∧
      pt (mH (LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.snd A A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  let i₁ := pt (mH (LinearMap.inl B M M)) (module_hom_comp_square_zero_section (R := R) _)
  let i₂ := pt (mH (LinearMap.inr B M M)) (module_hom_comp_square_zero_section (R := R) _)
  have hf : ∀ (u : M →ₗ[B] M × M), pt (ρ := r1 R B (M × M)) (TrivSqZeroExt.fstHom B B (M × M)).toRingHom fst_comp_square_zero_section ≫
      pt (mH u) (module_hom_comp_square_zero_section _) = pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section := fun u ↦
    pt_comp _ _ _ _ _ (by ext a <;> simp) _
  have hz : ∀ (u : M × M →ₗ[B] M) (v : M →ₗ[B] M × M), u ∘ₗ v = 0 →
      pt (mH u) (module_hom_comp_square_zero_section _) ≫ pt (mH v) (module_hom_comp_square_zero_section _) =
        pt (ρ := algebraMap R B) (TrivSqZeroExt.inlHom B M) rfl ≫
          pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section := fun u v huv ↦ by
    have hK : (mH u).comp (mH v) =
        (TrivSqZeroExt.inlHom B M).comp (TrivSqZeroExt.fstHom B B M).toRingHom :=
      RingHom.ext fun a ↦ TrivSqZeroExt.ext (by simp) (by simpa using LinearMap.congr_fun huv a.snd)
    have h3 : ((TrivSqZeroExt.inlHom B M).comp (TrivSqZeroExt.fstHom B B M).toRingHom).comp (r1 R B M) =
        r1 R B M := by ext r <;> simp
    exact (pt_comp _ _ _ _ _ hK h3).trans (pt_comp _ _ _ _ _ rfl h3).symm
  have hi : ∀ (u : M × M →ₗ[B] M) (v : M →ₗ[B] M × M), u ∘ₗ v = LinearMap.id →
      pt (mH u) (module_hom_comp_square_zero_section _) ≫ pt (mH v) (module_hom_comp_square_zero_section (R := R) _) = 𝟙 _ := fun u v huv ↦ by
    have hK : (mH u).comp (mH v) = RingHom.id _ :=
      RingHom.ext fun a ↦ TrivSqZeroExt.ext (by simp) (by simpa using LinearMap.congr_fun huv a.snd)
    exact (pt_comp _ _ _ _ _ rfl (by rw [hK]; rfl)).trans (pt_id _ hK _)
  have f1 : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y ≫
      CartesianMonoidalCategory.fst A A = x0 A B := by
    rw [← Category.assoc, hy, lift_fst]
  have s1 : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y ≫
      CartesianMonoidalCategory.snd A A = x0 A B := by
    rw [← Category.assoc, hy, lift_snd]
  have hx : ∀ {Z : Over (Sp R)} (a : Z ⟶ TT (algebraMap R B)), a ≫ x0 A B = toUnit Z ≫ η[A] := fun a ↦ by
    rw [← Category.assoc, toUnit_unique (a ≫ toUnit _) (toUnit _)]
  have h1 : ∀ {Z : Over (Sp R)} (a : Z ⟶ A), a ≫ (1 : A ⟶ A) = toUnit Z ≫ η[A] := fun a ↦ by
    rw [Hom.one_def, ← Category.assoc, toUnit_unique (a ≫ toUnit _) (toUnit _)]
  refine ⟨lift (i₁ ≫ y ≫ CartesianMonoidalCategory.fst A A) (i₂ ≫ y ≫ CartesianMonoidalCategory.snd A A),
    ?_, ?_, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, hf, f1]
    · rw [Category.assoc, lift_snd, lift_snd, ← Category.assoc, hf, s1]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← Category.assoc, hi _ _ (by ext <;> simp), Category.id_comp]
    · rw [Category.assoc, lift_snd, ← Category.assoc, hi _ _ (by ext <;> simp), Category.id_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, hi _ _ (by ext <;> simp),
        Category.id_comp, Category.comp_id]
    · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, hz _ _ (by ext <;> simp),
        Category.assoc, s1, hx, h1]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, hz _ _ (by ext <;> simp),
        Category.assoc, f1, hx, h1]
    · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, hi _ _ (by ext <;> simp),
        Category.id_comp, Category.comp_id]
end GlobalTheory.CompanionTheory.AxForm
