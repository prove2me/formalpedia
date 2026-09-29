-- Prove2me | solution 1 for NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0c575a4a-84e6-5410-9fff-01f8fd3f2cd8

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight
open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

noncomputable section

namespace C5aD4ai

section Local

variable {K : Type*} [NormedField K]

def entrySum (M : Matrix (Fin 2) (Fin 2) K) : ℝ := ‖M 0 0‖ + ‖M 0 1‖ + ‖M 1 0‖ + ‖M 1 1‖

def entryMax (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max (max ‖M 0 0‖ ‖M 0 1‖) (max ‖M 1 0‖ ‖M 1 1‖)

theorem entrySum_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entrySum M := by
  unfold entrySum; positivity

theorem norm_le_entrySum (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖M i j‖ ≤ entrySum M := by
  have h00 := norm_nonneg (M 0 0); have h01 := norm_nonneg (M 0 1)
  have h10 := norm_nonneg (M 1 0); have h11 := norm_nonneg (M 1 1)
  unfold entrySum
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> linarith

theorem entryMax_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entryMax M :=
  (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem norm_le_entryMax (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖M i j‖ ≤ entryMax M := by
  unfold entryMax
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem entryMax_le_one_of {M : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, ‖M i j‖ ≤ 1) : entryMax M ≤ 1 :=
  max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

theorem rowMaxNorm_le_entryMax (M : Matrix (Fin 2) (Fin 2) K) : rowMaxNorm M ≤ entryMax M :=
  le_max_right _ _

theorem entrySum_pos (g : GL (Fin 2) K) : 0 < entrySum (g : Matrix (Fin 2) (Fin 2) K) :=
  (rowMaxNorm_pos g).trans_le (max_le (norm_le_entrySum _ 1 0) (norm_le_entrySum _ 1 1))

theorem entryMax_pos (g : GL (Fin 2) K) : 0 < entryMax (g : Matrix (Fin 2) (Fin 2) K) :=
  (rowMaxNorm_pos g).trans_le (rowMaxNorm_le_entryMax _)

theorem mul_apply_one (g x : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    (g * x) 1 j = g 1 0 * x 0 j + g 1 1 * x 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_mul_apply_one_le (g x : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    ‖(g * x) 1 j‖ ≤ (‖g 1 0‖ + ‖g 1 1‖) * entrySum x := by
  rw [mul_apply_one]
  calc ‖g 1 0 * x 0 j + g 1 1 * x 1 j‖ ≤ ‖g 1 0‖ * ‖x 0 j‖ + ‖g 1 1‖ * ‖x 1 j‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖g 1 0‖ * entrySum x + ‖g 1 1‖ * entrySum x :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_le_entrySum x 0 j) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_le_entrySum x 1 j) (norm_nonneg _))
    _ = (‖g 1 0‖ + ‖g 1 1‖) * entrySum x := by ring

theorem rowNormSq_mul_le (g x : Matrix (Fin 2) (Fin 2) K) :
    rowNormSq (g * x) ≤ 4 * entrySum x ^ 2 * rowNormSq g := by
  have hsq : ∀ j, ‖(g * x) 1 j‖ ^ 2 ≤ ((‖g 1 0‖ + ‖g 1 1‖) * entrySum x) ^ 2 := fun j =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_mul_apply_one_le g x j) 2
  have hab : (‖g 1 0‖ + ‖g 1 1‖) ^ 2 ≤ 2 * (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖g 1 0‖ - ‖g 1 1‖)]
  have hS := entrySum_nonneg x
  unfold rowNormSq
  calc ‖(g * x) 1 0‖ ^ 2 + ‖(g * x) 1 1‖ ^ 2
      ≤ ((‖g 1 0‖ + ‖g 1 1‖) * entrySum x) ^ 2 + ((‖g 1 0‖ + ‖g 1 1‖) * entrySum x) ^ 2 :=
        add_le_add (hsq 0) (hsq 1)
    _ = 2 * (‖g 1 0‖ + ‖g 1 1‖) ^ 2 * entrySum x ^ 2 := by ring
    _ ≤ 2 * (2 * (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)) * entrySum x ^ 2 := by gcongr
    _ = 4 * entrySum x ^ 2 * (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) := by ring

def archLowerFactor (x : GL (Fin 2) K) : ℝ :=
  ‖(x : Matrix (Fin 2) (Fin 2) K).det‖ / (4 * entrySum (x : Matrix (Fin 2) (Fin 2) K) ^ 2)

def archUpperFactor (x : GL (Fin 2) K) : ℝ :=
  4 * entrySum ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2 * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖

theorem archLowerFactor_pos (x : GL (Fin 2) K) : 0 < archLowerFactor x :=
  div_pos (norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero)
    (mul_pos four_pos (pow_pos (entrySum_pos x) 2))

theorem archUpperFactor_nonneg (x : GL (Fin 2) K) : 0 ≤ archUpperFactor x :=
  mul_nonneg (mul_nonneg four_pos.le (pow_nonneg (entrySum_nonneg _) 2)) (norm_nonneg _)

theorem archLowerFactor_mul_le (g x : GL (Fin 2) K) :
    archLowerFactor x * localHeight g ≤ localHeight (g * x) := by
  have hrow := rowNormSq_mul_le (g : Matrix (Fin 2) (Fin 2) K) (x : Matrix (Fin 2) (Fin 2) K)
  have hpos := rowNormSq_pos (g * x)
  rw [Units.val_mul] at hpos
  have hS := entrySum_pos x
  have hg := rowNormSq_pos g
  unfold archLowerFactor localHeight
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  calc ‖(x : Matrix (Fin 2) (Fin 2) K).det‖ / (4 * entrySum (x : Matrix (Fin 2) (Fin 2) K) ^ 2)
        * (‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K))
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          / (4 * entrySum (x : Matrix (Fin 2) (Fin 2) K) ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)) := by
        rw [div_mul_div_comm]; ring
    _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          / rowNormSq ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hrow

theorem le_archUpperFactor_mul (g x : GL (Fin 2) K) :
    localHeight (g * x) ≤ archUpperFactor x * localHeight g := by
  have hrow := rowNormSq_mul_le ((g * x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [← Units.val_mul, mul_inv_cancel_right, Units.val_mul] at hrow
  have hpos := rowNormSq_pos (g * x)
  rw [Units.val_mul] at hpos
  have hg := rowNormSq_pos g
  unfold archUpperFactor localHeight
  rw [Units.val_mul, Matrix.det_mul, norm_mul, div_le_iff₀ hpos]
  have key : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * (4 * entrySum ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * rowNormSq ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K))) :=
    mul_le_mul_of_nonneg_left hrow (by positivity)
  calc ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) / rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
        field_simp
    _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * (4 * entrySum ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * rowNormSq ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)))
          / rowNormSq (g : Matrix (Fin 2) (Fin 2) K) :=
        div_le_div_of_nonneg_right key hg.le
    _ = 4 * entrySum ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          * (‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K))
          * rowNormSq ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) := by
        field_simp

theorem continuous_entrySum : Continuous (fun M : Matrix (Fin 2) (Fin 2) K => entrySum M) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) K => M) := continuous_id
  unfold entrySum
  exact ((((hc.matrix_elem 0 0).norm.add (hc.matrix_elem 0 1).norm).add
    (hc.matrix_elem 1 0).norm).add (hc.matrix_elem 1 1).norm)

theorem continuous_archLowerFactor : Continuous (archLowerFactor (K := K)) := by
  unfold archLowerFactor
  refine (Units.continuous_val.matrix_det.norm).div
    (continuous_const.mul ((continuous_entrySum.comp Units.continuous_val).pow 2)) fun x => ?_
  exact (mul_pos four_pos (pow_pos (entrySum_pos x) 2)).ne'

theorem continuous_archUpperFactor : Continuous (archUpperFactor (K := K)) := by
  unfold archUpperFactor
  exact (continuous_const.mul ((continuous_entrySum.comp Units.continuous_coe_inv).pow 2)).mul
    (Units.continuous_val.matrix_det.norm)

def finLowerFactor (x : GL (Fin 2) K) : ℝ :=
  ‖(x : Matrix (Fin 2) (Fin 2) K).det‖ / entryMax (x : Matrix (Fin 2) (Fin 2) K) ^ 2

def finUpperFactor (x : GL (Fin 2) K) : ℝ :=
  entryMax ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2 * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖

theorem finLowerFactor_pos (x : GL (Fin 2) K) : 0 < finLowerFactor x :=
  div_pos (norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero) (pow_pos (entryMax_pos x) 2)

theorem finUpperFactor_nonneg (x : GL (Fin 2) K) : 0 ≤ finUpperFactor x :=
  mul_nonneg (pow_nonneg (entryMax_nonneg _) 2) (norm_nonneg _)

variable [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (g x : Matrix (Fin 2) (Fin 2) K) :
    rowMaxNorm (g * x) ≤ rowMaxNorm g * entryMax x := by
  have h : ∀ j, ‖(g * x) 1 j‖ ≤ rowMaxNorm g * entryMax x := fun j => by
    rw [mul_apply_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (le_max_left _ _) (norm_le_entryMax x 0 j) (norm_nonneg _) (rowMaxNorm_nonneg g)
    · rw [norm_mul]
      exact mul_le_mul (le_max_right _ _) (norm_le_entryMax x 1 j) (norm_nonneg _) (rowMaxNorm_nonneg g)
  exact max_le (h 0) (h 1)

theorem finLowerFactor_mul_le (g x : GL (Fin 2) K) :
    finLowerFactor x * finLocalHeight g ≤ finLocalHeight (g * x) := by
  have hrow : rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2
      ≤ entryMax (x : Matrix (Fin 2) (Fin 2) K) ^ 2 * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2 := by
    rw [← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (rowMaxNorm_nonneg _) (rowMaxNorm_mul_le _ _) 2
  have hpos := rowMaxNorm_pos (g * x)
  rw [Units.val_mul] at hpos
  have hM := entryMax_pos x
  have hg := rowMaxNorm_pos g
  unfold finLowerFactor finLocalHeight
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  calc ‖(x : Matrix (Fin 2) (Fin 2) K).det‖ / entryMax (x : Matrix (Fin 2) (Fin 2) K) ^ 2
        * (‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2)
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          / (entryMax (x : Matrix (Fin 2) (Fin 2) K) ^ 2 * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2) := by
        rw [div_mul_div_comm]; ring
    _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          / rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hrow

theorem le_finUpperFactor_mul (g x : GL (Fin 2) K) :
    finLocalHeight (g * x) ≤ finUpperFactor x * finLocalHeight g := by
  have hrow0 := rowMaxNorm_mul_le ((g * x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [← Units.val_mul, mul_inv_cancel_right, Units.val_mul] at hrow0
  have hrow : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2
      ≤ entryMax ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
        * rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2 := by
    rw [← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (rowMaxNorm_nonneg _) hrow0 2
  have hpos := rowMaxNorm_pos (g * x)
  rw [Units.val_mul] at hpos
  have hg := rowMaxNorm_pos g
  unfold finUpperFactor finLocalHeight
  rw [Units.val_mul, Matrix.det_mul, norm_mul, div_le_iff₀ (pow_pos hpos 2)]
  have key : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * (entryMax ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2) :=
    mul_le_mul_of_nonneg_left hrow (by positivity)
  calc ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2 / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2 := by
        field_simp
    _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
        * (entryMax ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2)
          / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2 :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = entryMax ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
          * ‖(x : Matrix (Fin 2) (Fin 2) K).det‖
          * (‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2)
          * rowMaxNorm ((g : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K)) ^ 2 := by
        field_simp

theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  nlinarith [norm_nonneg (k : Matrix (Fin 2) (Fin 2) K).det,
    norm_nonneg ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det]

theorem one_le_finLowerFactor_of_integral (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    1 ≤ finLowerFactor k := by
  unfold finLowerFactor
  rw [norm_det_eq_one_of_integral k h h', le_div_iff₀ (pow_pos (entryMax_pos k) 2), one_mul]
  exact pow_le_one₀ (entryMax_nonneg _) (entryMax_le_one_of h)

theorem finUpperFactor_le_one_of_integral (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finUpperFactor k ≤ 1 := by
  unfold finUpperFactor
  rw [norm_det_eq_one_of_integral k h h', mul_one]
  exact pow_le_one₀ (entryMax_nonneg _) (entryMax_le_one_of h')

theorem finLocalHeight_mul_eq_of_integral (g k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  have hfpos := finLocalHeight_pos g
  refine le_antisymm ?_ ?_
  · calc finLocalHeight (g * k) ≤ finUpperFactor k * finLocalHeight g := le_finUpperFactor_mul g k
      _ ≤ 1 * finLocalHeight g :=
          mul_le_mul_of_nonneg_right (finUpperFactor_le_one_of_integral k h h') hfpos.le
      _ = finLocalHeight g := one_mul _
  · calc finLocalHeight g = 1 * finLocalHeight g := (one_mul _).symm
      _ ≤ finLowerFactor k * finLocalHeight g :=
          mul_le_mul_of_nonneg_right (one_le_finLowerFactor_of_integral k h h') hfpos.le
      _ ≤ finLocalHeight (g * k) := finLowerFactor_mul_le g k

end Local

section Global

variable {F : Type} [Field F] [NumberField F]

theorem finHeight_mul_eq_of_mem (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (h * k) = finHeight F h := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_eq_of_integral _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem eventually_integral (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, ‖(finComponent (𝓞 F) F v y : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) ∧
      ∀ i j, ‖(((finComponent (𝓞 F) F v y)⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((y⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

theorem exists_finHeight_mul_bounds (y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ L U : ℝ, 0 < L ∧ 0 ≤ U ∧ ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F),
      L * finHeight F h ≤ finHeight F (h * y) ∧ finHeight F (h * y) ≤ U * finHeight F h := by
  set cL : HeightOneSpectrum (𝓞 F) → ℝ := fun v => min 1 (finLowerFactor (finComponent (𝓞 F) F v y))
    with hcLdef
  set cU : HeightOneSpectrum (𝓞 F) → ℝ := fun v => max 1 (finUpperFactor (finComponent (𝓞 F) F v y))
    with hcUdef
  have hint := eventually_integral y
  have hcL : cL.HasFiniteMulSupport := by
    refine Filter.eventually_cofinite.mp (hint.mono fun v hv => ?_)
    exact min_eq_left (one_le_finLowerFactor_of_integral _ hv.1 hv.2)
  have hcU : cU.HasFiniteMulSupport := by
    refine Filter.eventually_cofinite.mp (hint.mono fun v hv => ?_)
    exact max_eq_left (finUpperFactor_le_one_of_integral _ hv.1 hv.2)
  have hcLpos : ∀ v, 0 < cL v := fun v => lt_min one_pos (finLowerFactor_pos _)
  have hcUnn : ∀ v, 0 ≤ cU v := fun v => zero_le_one.trans (le_max_left _ _)
  refine ⟨∏ᶠ v, cL v, ∏ᶠ v, cU v, ?_, finprod_nonneg hcUnn, fun h => ⟨?_, ?_⟩⟩
  · exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) hcLpos
  · have hB := hasFiniteMulSupport_finLocalHeight h
    have hA := hasFiniteMulSupport_finLocalHeight (h * y)
    unfold finHeight
    rw [← finprod_mul_distrib hcL hB]
    refine finprod_le_finprod (hcL.mul hB) (fun v => mul_nonneg (hcLpos v).le (finLocalHeight_pos _).le)
      hA fun v => ?_
    show cL v * finLocalHeight (finComponent (𝓞 F) F v h) ≤ finLocalHeight (finComponent (𝓞 F) F v (h * y))
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (finLocalHeight_pos _).le).trans
      (finLowerFactor_mul_le _ _)
  · have hB := hasFiniteMulSupport_finLocalHeight h
    have hA := hasFiniteMulSupport_finLocalHeight (h * y)
    unfold finHeight
    rw [← finprod_mul_distrib hcU hB]
    refine finprod_le_finprod hA (fun v => (finLocalHeight_pos _).le) (hcU.mul hB) fun v => ?_
    show finLocalHeight (finComponent (𝓞 F) F v (h * y)) ≤ cU v * finLocalHeight (finComponent (𝓞 F) F v h)
    rw [map_mul]
    exact (le_finUpperFactor_mul _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (finLocalHeight_pos _).le)

variable (F)

def archLower (y : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ w : InfinitePlace F, archLowerFactor (archComponent F w y) ^ w.mult

def archUpper (y : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ w : InfinitePlace F, archUpperFactor (archComponent F w y) ^ w.mult

theorem archLower_pos (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < archLower F y :=
  Finset.prod_pos fun _ _ => pow_pos (archLowerFactor_pos _) _

theorem archUpper_nonneg (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 ≤ archUpper F y :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (archUpperFactor_nonneg _) _

theorem archLower_mul_le (h y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archLower F y * archHeight F h ≤ archHeight F (h * y) := by
  unfold archLower archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => mul_nonneg (pow_nonneg (archLowerFactor_pos _).le _)
    (pow_nonneg (localHeight_pos _).le _)) fun w _ => ?_
  rw [← mul_pow, map_mul]
  exact pow_le_pow_left₀ (mul_nonneg (archLowerFactor_pos _).le (localHeight_pos _).le)
    (archLowerFactor_mul_le _ _) _

theorem le_archUpper_mul (h y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (h * y) ≤ archUpper F y * archHeight F h := by
  unfold archUpper archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (localHeight_pos _).le _) fun w _ => ?_
  rw [← mul_pow, map_mul]
  exact pow_le_pow_left₀ (localHeight_pos _).le (le_archUpperFactor_mul _ _) _

theorem continuous_archLower : Continuous (archLower F) := by
  unfold archLower
  exact continuous_finsetProd _ fun w _ =>
    (continuous_archLowerFactor.comp (continuous_archComponent F w)).pow _

theorem continuous_archUpper : Continuous (archUpper F) := by
  unfold archUpper
  exact continuous_finsetProd _ fun w _ =>
    (continuous_archUpperFactor.comp (continuous_archComponent F w)).pow _

theorem main (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ κ K : ℝ, 0 < κ ∧ ∀ (g : AdelicGL2 (𝓞 F) F), ∀ x ∈ C,
      κ * adelicHeight F g ≤ adelicHeight F (g * x) ∧ adelicHeight F (g * x) ≤ K * adelicHeight F g := by
  refine hC.induction_on
    (p := fun S => ∃ κ K : ℝ, 0 < κ ∧ ∀ (g : AdelicGL2 (𝓞 F) F), ∀ x ∈ S,
      κ * adelicHeight F g ≤ adelicHeight F (g * x) ∧ adelicHeight F (g * x) ≤ K * adelicHeight F g)
    ?_ ?_ ?_ ?_
  · exact ⟨1, 0, one_pos, fun g x hx => hx.elim⟩
  · rintro S T hST ⟨κ, K, hκ, hb⟩
    exact ⟨κ, K, hκ, fun g x hx => hb g x (hST hx)⟩
  · rintro S T ⟨κ₁, K₁, hκ₁, hb₁⟩ ⟨κ₂, K₂, hκ₂, hb₂⟩
    refine ⟨min κ₁ κ₂, max K₁ K₂, lt_min hκ₁ hκ₂, fun g x hx => ?_⟩
    have hg := (adelicHeight_pos g).le
    rcases hx with hx | hx
    · obtain ⟨hl, hu⟩ := hb₁ g x hx
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hg).trans hl,
        hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg)⟩
    · obtain ⟨hl, hu⟩ := hb₂ g x hx
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hg).trans hl,
        hu.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg)⟩
  · intro x₀ _
    obtain ⟨L, U, hL, hU, hLU⟩ := exists_finHeight_mul_bounds (glFin (𝓞 F) F x₀)
    set aL := archLower F (glArch (𝓞 F) F x₀) with haLdef
    set aU := archUpper F (glArch (𝓞 F) F x₀) with haUdef
    have haL : 0 < aL := archLower_pos F _
    have haU : 0 ≤ aU := archUpper_nonneg F _
    set t : Set (AdelicGL2 (𝓞 F) F) :=
      ({x | aL / 2 < archLower F (glArch (𝓞 F) F x)} ∩ {x | archUpper F (glArch (𝓞 F) F x) < aU + 1}) ∩
        {x | glFin (𝓞 F) F (x₀⁻¹ * x) ∈ finiteIntegralGL2 (𝓞 F) F} with htdef
    have ht : t ∈ nhds x₀ := by
      have h1 : IsOpen {x : AdelicGL2 (𝓞 F) F | aL / 2 < archLower F (glArch (𝓞 F) F x)} :=
        isOpen_lt continuous_const ((continuous_archLower F).comp (continuous_glArch (𝓞 F) F))
      have h2 : IsOpen {x : AdelicGL2 (𝓞 F) F | archUpper F (glArch (𝓞 F) F x) < aU + 1} :=
        isOpen_lt ((continuous_archUpper F).comp (continuous_glArch (𝓞 F) F)) continuous_const
      have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by simp
      have h3 : IsOpen {x : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F (x₀⁻¹ * x) ∈ finiteIntegralGL2 (𝓞 F) F} :=
        (isOpen_finiteLevelZero (𝓞 F) F htop).preimage
          ((continuous_glFin (𝓞 F) F).comp (continuous_const_mul x₀⁻¹))
      refine ((h1.inter h2).inter h3).mem_nhds ⟨⟨?_, ?_⟩, ?_⟩
      · show aL / 2 < archLower F (glArch (𝓞 F) F x₀)
        exact half_lt_self haL
      · show archUpper F (glArch (𝓞 F) F x₀) < aU + 1
        exact lt_add_one _
      · show glFin (𝓞 F) F (x₀⁻¹ * x₀) ∈ finiteIntegralGL2 (𝓞 F) F
        rw [inv_mul_cancel, map_one]
        exact one_mem _
    refine ⟨t, mem_nhdsWithin_of_mem_nhds ht, aL / 2 * L, (aU + 1) * U, mul_pos (half_pos haL) hL,
      fun g x hx => ?_⟩
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hfin : finHeight F (glFin (𝓞 F) F g * glFin (𝓞 F) F x)
        = finHeight F (glFin (𝓞 F) F g * glFin (𝓞 F) F x₀) := by
      have heq : glFin (𝓞 F) F g * glFin (𝓞 F) F x
          = glFin (𝓞 F) F g * glFin (𝓞 F) F x₀ * glFin (𝓞 F) F (x₀⁻¹ * x) := by
        rw [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      rw [heq, finHeight_mul_eq_of_mem _ hx3]
    obtain ⟨hfl, hfu⟩ := hLU (glFin (𝓞 F) F g)
    have hapos := archHeight_pos F (glArch (𝓞 F) F g)
    have hfpos := finHeight_pos (glFin (𝓞 F) F g)
    have harchl : aL / 2 * archHeight F (glArch (𝓞 F) F g)
        ≤ archHeight F (glArch (𝓞 F) F g * glArch (𝓞 F) F x) :=
      (mul_le_mul_of_nonneg_right hx1.le hapos.le).trans (archLower_mul_le F _ _)
    have harchu : archHeight F (glArch (𝓞 F) F g * glArch (𝓞 F) F x)
        ≤ (aU + 1) * archHeight F (glArch (𝓞 F) F g) :=
      (le_archUpper_mul F _ _).trans (mul_le_mul_of_nonneg_right hx2.le hapos.le)
    unfold adelicHeight
    rw [map_mul, map_mul, hfin]
    constructor
    · calc aL / 2 * L * (archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g))
          = (aL / 2 * archHeight F (glArch (𝓞 F) F g)) * (L * finHeight F (glFin (𝓞 F) F g)) := by ring
        _ ≤ archHeight F (glArch (𝓞 F) F g * glArch (𝓞 F) F x)
              * finHeight F (glFin (𝓞 F) F g * glFin (𝓞 F) F x₀) :=
            mul_le_mul harchl hfl (mul_nonneg hL.le hfpos.le) (archHeight_pos F _).le
    · calc archHeight F (glArch (𝓞 F) F g * glArch (𝓞 F) F x)
              * finHeight F (glFin (𝓞 F) F g * glFin (𝓞 F) F x₀)
          ≤ ((aU + 1) * archHeight F (glArch (𝓞 F) F g)) * (U * finHeight F (glFin (𝓞 F) F g)) :=
            mul_le_mul harchu hfu (finHeight_pos _).le
              (mul_nonneg (add_nonneg haU zero_le_one) hapos.le)
        _ = (aU + 1) * U * (archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)) := by ring

end Global

end C5aD4ai

end

open C5aD4ai in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ κ K : ℝ, 0 < κ ∧ ∀ (g : AdelicGL2 (𝓞 F) F), ∀ x ∈ C,
      κ * adelicHeight F g ≤ adelicHeight F (g * x) ∧ adelicHeight F (g * x) ≤ K * adelicHeight F g :=
  C5aD4ai.main F C hC

end S_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
end P2MW
export P2MW.S_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact (solution)
