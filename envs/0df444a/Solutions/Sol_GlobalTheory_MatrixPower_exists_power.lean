-- Prove2me | solution 1 for GlobalTheory.MatrixPower.exists_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:45.569807+00:00
-- url     : https://prove2.me/submissions/2aee3842-4560-4a5d-b242-03dc01890980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction
import Theorems.Thm_GlobalTheory_MatrixPower_exists_grpObj_retract
import Theorems.Thm_GlobalTheory_MatrixPower_comp_prod
import Theorems.Thm_GlobalTheory_MatrixPower_prod_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.MatrixPower
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable [BraidedCategory C]
namespace GlobalTheory.MatrixPower
theorem _root_.solution [HasEqualizers C] {n : Type*} [Fintype n] [DecidableEq n] (o : n)
    (G : C) [GrpObj G] [IsCommMonObj G] (ρ : Matrix n n ℤ → (G ⟶ G))
    (hρ : ∀ m, IsMonHom (ρ m)) (hmul : ∀ m m', ρ (m * m') = ρ m' ≫ ρ m)
    (hadd : ∀ m m', ρ (m + m') = ρ m * ρ m') (hone : ρ 1 = 𝟙 G) :
    ∃ (A : C) (_ : GrpObj A) (_ : IsCommMonObj A) (_ : Retract A G) (pr : n → (G ⟶ A)),
      (∀ u, IsMonHom (pr u)) ∧
      (∀ (T : C) (y : n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧
      ∀ m u, ρ m ≫ pr u = ∏ v, pr v ^ m u v := by
  have : ∀ m, IsMonHom (ρ m) := hρ
  have hc : ∀ a b : Matrix n n ℤ, ρ a ≫ ρ b = ρ (b * a) := fun a b => (hmul b a).symm
  have h0 : ρ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hneg : ∀ a, ρ (-a) = (ρ a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsum : ∀ (s : Finset n) (f : n → Matrix n n ℤ), ρ (∑ v ∈ s, f v) = ∏ v ∈ s, ρ (f v) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have hzs : ∀ (k : ℤ) (a : Matrix n n ℤ), ρ (k • a) = ρ a ^ k := by
    intro k a
    refine Int.induction_on k ?_ ?_ ?_
    · rw [zero_smul, h0, zpow_zero]
    · intro j ih
      rw [add_smul, one_smul, hadd, ih, zpow_add_one]
    · intro j ih
      rw [sub_smul, one_smul, sub_eq_add_neg, hadd, ih, hneg, zpow_sub_one]
  have hidem : ρ (Matrix.single o o 1) ≫ ρ (Matrix.single o o 1) =
      ρ (Matrix.single o o 1) ≫ 𝟙 G := by
    rw [Category.comp_id, hc, Matrix.single_mul_single_same, _root_.mul_one]
  obtain ⟨A, i, r, hir, hri⟩ : ∃ (A : C) (i : A ⟶ G) (r : G ⟶ A),
      i ≫ r = 𝟙 A ∧ r ≫ i = ρ (Matrix.single o o 1) := by
    refine ⟨equalizer (ρ (Matrix.single o o 1)) (𝟙 G), equalizer.ι _ _, equalizer.lift _ hidem,
      ?_, equalizer.lift_ι _ _⟩
    apply equalizer.hom_ext
    rw [Category.assoc, equalizer.lift_ι, Category.id_comp]
    exact (equalizer.condition _ _).trans (Category.comp_id _)
  have hmono : Mono i := (SplitMono.mk r hir).mono
  have : IsMonHom (r ≫ i) := by rw [hri]; infer_instance
  obtain ⟨gA, hi, hr⟩ := exists_grpObj_retract i r hir
  have hcA : IsCommMonObj A :=
    (isCommMonObj_iff_isMulCommutative _).2 fun X => ⟨⟨fun a b => by
      show a * b = b * a
      rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]⟩⟩
  refine ⟨A, gA, hcA, ⟨i, r, hir⟩,
    fun u => ρ (Matrix.single o u 1) ≫ r, fun u => inferInstance, ?_, ?_⟩
  · intro T y
    refine ⟨∏ v, y v ≫ i ≫ ρ (Matrix.single v o 1), fun u => ?_, fun x hx => ?_⟩
    · dsimp only
      rw [prod_comp, Finset.prod_eq_single u]
      · have h3 : ρ (Matrix.single u o 1) ≫ ρ (Matrix.single o u 1) ≫ r = r ≫ i ≫ r := by
          rw [← Category.assoc, hc, Matrix.single_mul_single_same, _root_.mul_one, ← hri,
            Category.assoc]
        simp only [Category.assoc]
        rw [h3, reassoc_of% hir, hir, Category.comp_id]
      · intro v _ hv
        have h3 : ρ (Matrix.single v o 1) ≫ ρ (Matrix.single o u 1) ≫ r = 1 := by
          have h5 : Matrix.single o u (1 : ℤ) * Matrix.single v o 1 = 0 := by
            simp [Ne.symm hv]
          rw [← Category.assoc, hc, h5, h0, MonObj.one_comp]
        simp only [Category.assoc]
        rw [h3, MonObj.comp_one, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ u) h
    · dsimp only at hx
      have h1 : (1 : Matrix n n ℤ) = ∑ v, Matrix.single v v 1 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.sum_apply, Matrix.single_apply]
        · rw [Matrix.sum_apply, Finset.sum_eq_zero]
          · exact Matrix.one_apply_ne hab
          · intro v _
            rw [Matrix.single_apply]
            split_ifs with h
            · exact absurd (h.1.symm.trans h.2) hab
            · rfl
      calc x = x ≫ ρ 1 := by rw [hone, Category.comp_id]
        _ = ∏ v, x ≫ ρ (Matrix.single v v 1) := by rw [h1, hsum, comp_prod]
        _ = _ := by
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← hx v]
          have h4 : ρ (Matrix.single o v 1) ≫ r ≫ i ≫ ρ (Matrix.single v o 1) =
              ρ (Matrix.single v v 1) := by
            rw [reassoc_of% hri, hc, Matrix.single_mul_single_same, hc,
              Matrix.single_mul_single_same]
            simp only [_root_.mul_one]
          simp only [Category.assoc, h4]
  · intro m u
    dsimp only
    have hrow : Matrix.single o u (1 : ℤ) * m = ∑ v, m u v • Matrix.single o v 1 := by
      ext a b
      by_cases ha : a = o
      · subst ha
        simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, Matrix.sum_apply, Ne.symm ha]
    have := hcA
    rw [← Category.assoc, hc, hrow, hsum, prod_comp]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hzs, GrpObj.zpow_comp]
end GlobalTheory.MatrixPower
