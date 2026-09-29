-- Prove2me | solution 1 for LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e1d4c37a-e63d-5644-8117-f172015745ff

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq

set_option autoImplicit false

noncomputable section

open scoped Real
open AutomorphicForm Matrix

private theorem exp_log_half {q : ℝ} (hq : 0 < q) : Real.exp (Real.log q / 2) = Real.sqrt q := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
  congr 1
  ring

private theorem exp_log_half_mul_self {y : ℝ} (hy : 0 < y) :
    Real.exp (Real.log y / 2) * Real.exp (Real.log y / 2) = y := by
  rw [← Real.exp_add, add_halves, Real.exp_log hy]

private theorem splitTorusGL2_log_half_mul_splitTorusGL2 {y : ℝ} (hy : 0 < y) (t : ℝ) :
    splitTorusGL2 (Real.log y / 2) * splitTorusGL2 t
      = splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2) := by
  rw [← splitTorusGL2_add, Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 1
  ring

private theorem splitTorusGL2_log_half_mul_splitTorusGL2_log_half {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    splitTorusGL2 (Real.log y / 2) * splitTorusGL2 (Real.log y' / 2)
      = splitTorusGL2 (Real.log (y * y') / 2) := by
  rw [← splitTorusGL2_add, Real.log_mul hy.ne' hy'.ne']
  congr 1
  ring

private theorem splitTorusGL2_log_half_mul_unipotentGL2 {y : ℝ} (hy : 0 < y) (x : ℝ) :
    splitTorusGL2 (Real.log y / 2) * unipotentGL2 x
      = unipotentGL2 (y * x) * splitTorusGL2 (Real.log y / 2) := by
  have h2 : Real.exp (Real.log y / 2) ^ 2 = y := by rw [sq]; exact exp_log_half_mul_self hy
  have h0 : Real.exp (Real.log y / 2) ≠ 0 := (Real.exp_pos _).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, splitTorusGL2_coe, unipotentGL2_coe, Real.exp_neg]
  field_simp
  linear_combination x * h2

private def rotK (s : ℝ) : GL (Fin 2) ℝ where
  val := !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
    s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹]
  inv := !![(Real.sqrt (1 + s ^ 2))⁻¹, s * (Real.sqrt (1 + s ^ 2))⁻¹;
    -(s * (Real.sqrt (1 + s ^ 2))⁻¹), (Real.sqrt (1 + s ^ 2))⁻¹]
  val_inv := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])
  inv_val := by
    have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; nlinarith [hr])

private theorem rotK_coe (s : ℝ) :
    (rotK s : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹);
          s * (Real.sqrt (1 + s ^ 2))⁻¹, (Real.sqrt (1 + s ^ 2))⁻¹] :=
  rfl

private theorem rotK_mem (s : ℝ) : rotK s ∈ rowIsometrySubgroup₀ ℝ := by
  have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hdet : (rotK s : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [rotK_coe, Matrix.det_fin_two_of]
    field_simp
    nlinarith [hr]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rotK_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    nlinarith [hr]

private theorem firstRowℂ_rotK (s : ℝ) :
    firstRowℂ (rotK s) = ⟨(Real.sqrt (1 + s ^ 2))⁻¹, -(s * (Real.sqrt (1 + s ^ 2))⁻¹)⟩ :=
  rfl

private theorem unipotentGL2_mul_lowerUnipotentGL2 (t s : ℝ) :
    unipotentGL2 t * lowerUnipotentGL2 s
      = unipotentGL2 (t + s / (1 + s ^ 2)) * splitTorusGL2 (-(Real.log (1 + s ^ 2) / 2)) * rotK s := by
  have hq : 0 < 1 + s ^ 2 := by positivity
  have hq0 : 1 + s ^ 2 ≠ 0 := hq.ne'
  have hr : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt hq.le
  have hr0 : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have he : Real.exp (Real.log (1 + s ^ 2) / 2) = Real.sqrt (1 + s ^ 2) := exp_log_half hq
  have ha : (splitTorusGL2 (-(Real.log (1 + s ^ 2) / 2)) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(Real.sqrt (1 + s ^ 2))⁻¹, 0; 0, Real.sqrt (1 + s ^ 2)] := by
    rw [splitTorusGL2_coe, neg_neg, Real.exp_neg, he]
  ext i j
  simp only [Units.val_mul, ha, unipotentGL2_coe, lowerUnipotentGL2_coe, rotK_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr0]
  all_goals (field_simp <;> (rw [hr]; ring1))

private theorem splitTorusGL2_mul_unipotentGL2_mul_lowerUnipotentGL2 {y : ℝ} (hy : 0 < y) (t s : ℝ) :
    splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s
      = unipotentGL2 (y * (t + s / (1 + s ^ 2)))
          * splitTorusGL2 (Real.log (y * (1 + s ^ 2)⁻¹) / 2) * rotK s := by
  have hq : 0 < (1 + s ^ 2)⁻¹ := inv_pos.mpr (by positivity)
  have hl : -(Real.log (1 + s ^ 2) / 2) = Real.log ((1 + s ^ 2)⁻¹) / 2 := by rw [Real.log_inv, neg_div]
  rw [mul_assoc, unipotentGL2_mul_lowerUnipotentGL2, hl, ← mul_assoc, ← mul_assoc,
    splitTorusGL2_log_half_mul_unipotentGL2 hy, mul_assoc (unipotentGL2 _),
    splitTorusGL2_log_half_mul_splitTorusGL2_log_half hy hq]

private theorem J_mul_unipotentGL2 (x : ℝ) :
    UpperHalfPlane.J * unipotentGL2 x = unipotentGL2 (-x) * UpperHalfPlane.J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, UpperHalfPlane.val_J]

private theorem archFlowMatrix_H (t : ℝ) : archFlowMatrix ArchDir.H t = splitTorusGL2 t := rfl
private theorem archFlowMatrix_E (t : ℝ) : archFlowMatrix ArchDir.E t = unipotentGL2 t := rfl
private theorem archFlowMatrix_Fm (t : ℝ) : archFlowMatrix ArchDir.Fm t = lowerUnipotentGL2 t := rfl

private theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

private def rotKℂ (s : ℝ) : ℂ :=
  (((Real.sqrt (1 + s ^ 2))⁻¹ : ℝ) : ℂ) + ((-(s * (Real.sqrt (1 + s ^ 2))⁻¹) : ℝ) : ℂ) * Complex.I

private theorem firstRowℂ_rotK_eq (s : ℝ) : firstRowℂ (rotK s) = rotKℂ s := by
  rw [firstRowℂ_rotK, rotKℂ, Complex.mk_eq_add_mul_I]

private theorem rotKℂ_zero : rotKℂ 0 = 1 := by
  simp [rotKℂ]

private theorem closed_form (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (c : ℝ)
    (hψc : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * π * Complex.I * (c * x : ℝ)) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    {y : ℝ} (hy : 0 < y) (t s : ℝ) :
    F (splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s)
      = Complex.exp (2 * π * Complex.I * (c * (y * (t + s / (1 + s ^ 2))) : ℝ)) * rotKℂ s ^ k₀
          * F (splitTorusGL2 (Real.log (y * (1 + s ^ 2)⁻¹) / 2)) := by
  have h2 : F (unipotentGL2 (y * (t + s / (1 + s ^ 2))) * splitTorusGL2 (Real.log (y * (1 + s ^ 2)⁻¹) / 2)
        * rotK s)
      = (archWeightCharℝ k₀ ⟨rotK s, rotK_mem s⟩ : ℂ)
          * F (unipotentGL2 (y * (t + s / (1 + s ^ 2))) * splitTorusGL2 (Real.log (y * (1 + s ^ 2)⁻¹) / 2)) :=
    hk ⟨rotK s, rotK_mem s⟩ _
  rw [splitTorusGL2_mul_unipotentGL2_mul_lowerUnipotentGL2 hy, h2, hψc, archWeightCharℝ_apply_coe]
  show firstRowℂ (rotK s) ^ k₀ * _ = _
  rw [firstRowℂ_rotK_eq]
  ring

private theorem hasDerivAt_one_add_sq_zero : HasDerivAt (fun s : ℝ => 1 + s ^ 2) 0 0 := by
  simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)

private theorem hasDerivAt_inv_sqrt_zero : HasDerivAt (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) 0 0 := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2)) (1 / (2 * Real.sqrt (1 + (0 : ℝ) ^ 2)) * 0) 0 :=
    (Real.hasDerivAt_sqrt (x := 1 + (0 : ℝ) ^ 2) (by norm_num)).comp (0 : ℝ) hasDerivAt_one_add_sq_zero
  have h2 := h1.inv (by simp)
  simp at h2
  exact h2

private theorem hasDerivAt_rotKℂ_zero : HasDerivAt rotKℂ (-Complex.I) 0 := by
  have hre := hasDerivAt_inv_sqrt_zero.ofReal_comp
  have him := (((hasDerivAt_id (0 : ℝ)).fun_mul hasDerivAt_inv_sqrt_zero).fun_neg).ofReal_comp
  have h := hre.fun_add (him.mul_const Complex.I)
  convert h using 1
  · rfl
  · rfl
  simp

private theorem hasDerivAt_rotKℂ_zpow_zero (k₀ : ℤ) :
    HasDerivAt (fun s : ℝ => rotKℂ s ^ k₀) (-(k₀ : ℂ) * Complex.I) 0 := by
  have hz : HasDerivAt (fun z : ℂ => z ^ k₀) ((k₀ : ℂ) * (1 : ℂ) ^ (k₀ - 1)) (1 : ℂ) :=
    hasDerivAt_zpow k₀ (1 : ℂ) (Or.inl one_ne_zero)
  have h := hz.comp_of_eq (0 : ℝ) hasDerivAt_rotKℂ_zero rotKℂ_zero.symm
  refine h.congr_deriv (Eq.symm ?_)
  rw [_root_.one_zpow]
  ring

private theorem hasDerivAt_shift_zero (t : ℝ) : HasDerivAt (fun s : ℝ => t + s / (1 + s ^ 2)) 1 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).div hasDerivAt_one_add_sq_zero (by norm_num)).const_add t
  simpa using h

private theorem hasDerivAt_scale_zero (y : ℝ) : HasDerivAt (fun s : ℝ => y * (1 + s ^ 2)⁻¹) 0 0 := by
  have h := (hasDerivAt_one_add_sq_zero.inv (by norm_num)).const_mul y
  simpa using h

private theorem deriv_s_closed_form (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (c : ℝ)
    (hψc : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * π * Complex.I * (c * x : ℝ)) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    {y : ℝ} (hy : 0 < y) (hf : DifferentiableAt ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y)
    (t : ℝ) :
    deriv (fun s : ℝ => F (splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s)) 0
      = Complex.exp (2 * π * Complex.I * (c * (y * t) : ℝ))
          * (Complex.I * (2 * π * c * y - k₀)) * F (splitTorusGL2 (Real.log y / 2)) := by

  set f : ℝ → ℂ := fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)) with hfdef
  have hfun : (fun s : ℝ => F (splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s))
      = fun s : ℝ => Complex.exp (2 * π * Complex.I * (c * (y * (t + s / (1 + s ^ 2))) : ℝ)) * rotKℂ s ^ k₀
          * f (y * (1 + s ^ 2)⁻¹) := by
    funext s
    exact closed_form F k₀ c hψc hk hy t s

  have hE : HasDerivAt (fun s : ℝ => Complex.exp (2 * π * Complex.I * (c * (y * (t + s / (1 + s ^ 2))) : ℝ)))
      (Complex.exp (2 * π * Complex.I * (c * (y * (t + 0 / (1 + (0 : ℝ) ^ 2))) : ℝ))
        * (2 * π * Complex.I * ((c * (y * 1) : ℝ) : ℂ))) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => c * (y * (t + s / (1 + s ^ 2)))) (c * (y * 1)) 0 :=
      ((hasDerivAt_shift_zero t).const_mul y).const_mul c
    exact ((h1.ofReal_comp).const_mul (2 * π * Complex.I)).cexp

  have hP := hasDerivAt_rotKℂ_zpow_zero k₀

  have hQ : HasDerivAt (fun s : ℝ => f (y * (1 + s ^ 2)⁻¹)) ((0 : ℝ) • deriv f y) 0 := by
    have hg : HasDerivAt f (deriv f y) y := hf.hasDerivAt
    exact hg.scomp_of_eq (0 : ℝ) (hasDerivAt_scale_zero y) (by simp)
  have hEPQ := (hE.fun_mul hP).fun_mul hQ
  rw [hfun, hEPQ.deriv]
  simp only [zero_smul, mul_zero, add_zero, zero_div, rotKℂ_zero, _root_.one_zpow, mul_one, inv_one, pow_two,
    hfdef]
  push_cast
  ring

private theorem deriv_E_Fm (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (c : ℝ)
    (hψc : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * π * Complex.I * (c * x : ℝ)) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    {y : ℝ} (hy : 0 < y) (hf : DifferentiableAt ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
        F (splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s)) 0) 0
      = -(2 * π * c * y * (2 * π * c * y - k₀)) * F (splitTorusGL2 (Real.log y / 2)) := by
  have hfun : (fun t : ℝ => deriv (fun s : ℝ =>
        F (splitTorusGL2 (Real.log y / 2) * unipotentGL2 t * lowerUnipotentGL2 s)) 0)
      = fun t : ℝ => Complex.exp (2 * π * Complex.I * (c * (y * t) : ℝ))
          * (Complex.I * (2 * π * c * y - k₀)) * F (splitTorusGL2 (Real.log y / 2)) := by
    funext t
    exact deriv_s_closed_form F k₀ c hψc hk hy hf t
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => c * (y * t)) (c * (y * 1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul y).const_mul c
  have hE := ((h1.ofReal_comp).const_mul (2 * π * Complex.I)).cexp
  have h := (hE.mul_const (Complex.I * (2 * π * c * y - k₀))).mul_const (F (splitTorusGL2 (Real.log y / 2)))
  rw [h.deriv]
  simp only [mul_zero, mul_one, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  push_cast
  linear_combination (2 * π * c * y * (2 * π * c * y - k₀) * F (splitTorusGL2 (Real.log y / 2))) * Complex.I_mul_I

private theorem deriv_H (F : GL (Fin 2) ℝ → ℂ) {y : ℝ} (hy : 0 < y)
    (hf : DifferentiableAt ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y) :
    deriv (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * splitTorusGL2 t)) 0
      = 2 * y * deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y := by
  set f : ℝ → ℂ := fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)) with hfdef
  have hfun : (fun t : ℝ => F (splitTorusGL2 (Real.log y / 2) * splitTorusGL2 t))
      = fun t : ℝ => f (y * Real.exp (2 * t)) := by
    funext t
    rw [splitTorusGL2_log_half_mul_splitTorusGL2 hy]
  rw [hfun]
  have hg : HasDerivAt (fun t : ℝ => y * Real.exp (2 * t)) (2 * y) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp.const_mul y
    convert h using 1
    · rfl
    · rfl
    simp [mul_comm]
  have hcomp : HasDerivAt (fun t : ℝ => f (y * Real.exp (2 * t))) ((2 * y) • deriv f y) 0 :=
    hf.hasDerivAt.scomp_of_eq (0 : ℝ) hg (by simp)
  rw [hcomp.deriv, Complex.real_smul]
  push_cast
  ring

private theorem deriv_H_H (F : GL (Fin 2) ℝ → ℂ) {y : ℝ} (hy : 0 < y)
    (hf : ∀ y' : ℝ, 0 < y' → DifferentiableAt ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y')
    (hf2 : DifferentiableAt ℝ (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
        F (splitTorusGL2 (Real.log y / 2) * splitTorusGL2 t * splitTorusGL2 s)) 0) 0
      = 4 * y * deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y
          + 4 * y ^ 2 * deriv (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y := by
  set f : ℝ → ℂ := fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)) with hfdef
  have hfun : (fun t : ℝ => deriv (fun s : ℝ =>
        F (splitTorusGL2 (Real.log y / 2) * splitTorusGL2 t * splitTorusGL2 s)) 0)
      = fun t : ℝ => 2 * ((y * Real.exp (2 * t) : ℝ) : ℂ) * deriv f (y * Real.exp (2 * t)) := by
    funext t
    have hyt : 0 < y * Real.exp (2 * t) := mul_pos hy (Real.exp_pos _)
    rw [splitTorusGL2_log_half_mul_splitTorusGL2 hy]
    exact deriv_H F hyt (hf _ hyt)
  rw [hfun]
  have hg : HasDerivAt (fun t : ℝ => y * Real.exp (2 * t)) (2 * y) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp.const_mul y
    convert h using 1
    · rfl
    · rfl
    simp [mul_comm]
  have h1 : HasDerivAt (fun t : ℝ => ((y * Real.exp (2 * t) : ℝ) : ℂ)) ((2 * y : ℝ) : ℂ) 0 := hg.ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => deriv f (y * Real.exp (2 * t))) ((2 * y) • deriv (deriv f) y) 0 :=
    hf2.hasDerivAt.scomp_of_eq (0 : ℝ) hg (by simp)
  have h := (h1.const_mul (2 : ℂ)).fun_mul h2
  rw [h.deriv]
  simp only [mul_zero, Real.exp_zero, mul_one, Complex.real_smul]
  push_cast
  ring

private theorem torus_ode (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (ν : ℂ) (c : ℝ)
    (hψc : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * π * Complex.I * (c * x : ℝ)) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    (hΩ : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => F (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * F m)
    (hf : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) y)
    (hf2 : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y)
    {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y
      + (1 / 4 - ν ^ 2 + 2 * π * (c * k₀) * y - 4 * π ^ 2 * c ^ 2 * y ^ 2) * F (splitTorusGL2 (Real.log y / 2))
        = 0 := by
  have h := hΩ (splitTorusGL2 (Real.log y / 2))
  simp only [archFlowMatrix_H, archFlowMatrix_E, archFlowMatrix_Fm] at h
  rw [deriv_H_H F hy hf (hf2 y hy), deriv_H F hy (hf y hy), deriv_E_Fm F k₀ c hψc hk hy (hf y hy)] at h
  linear_combination (-1 : ℂ) * h

private theorem contDiffOn_torusFn {n : WithTop ℕ∞} (F : GL (Fin 2) ℝ → ℂ)
    (hF : ContDiffOn ℝ n
      (fun e : Fin 2 → Fin 2 → ℝ =>
        F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0})
    (P : GL (Fin 2) ℝ) :
    ContDiffOn ℝ n (fun y : ℝ => F (P * splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ := fun y hy => Set.mem_compl_singleton_iff.mpr (ne_of_gt hy)
  have hl : ContDiffOn ℝ n (fun y : ℝ => Real.log y / 2) (Set.Ioi 0) :=
    (Real.contDiffOn_log.mono hsub).div_const 2
  have hexp : ContDiffOn ℝ n (fun y : ℝ => Real.exp (Real.log y / 2)) (Set.Ioi 0) :=
    Real.contDiff_exp.comp_contDiffOn hl
  have hexp' : ContDiffOn ℝ n (fun y : ℝ => Real.exp (-(Real.log y / 2))) (Set.Ioi 0) :=
    Real.contDiff_exp.comp_contDiffOn hl.neg

  have hgs : ContDiffOn ℝ n
      (fun (y : ℝ) (i j : Fin 2) =>
        ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (Set.Ioi 0) := by
    refine contDiffOn_pi' fun i => contDiffOn_pi' fun j => ?_
    fin_cases j <;>
      simp only [Units.val_mul, splitTorusGL2_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_zero, zero_add, add_zero]
    · exact contDiffOn_const.mul hexp
    · exact contDiffOn_const.mul hexp'
  have hmaps : Set.MapsTo
      (fun (y : ℝ) (i j : Fin 2) =>
        ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (Set.Ioi 0) {e | (Matrix.of e).det ≠ 0} := by
    intro y _
    show (Matrix.of fun i j =>
      ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0
    have : (Matrix.of fun i j =>
        ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        = ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j; rfl
    rw [this, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  refine (hF.comp hgs hmaps).congr fun y hy => ?_
  have hdet : (Matrix.of fun i j =>
      ((P * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j).det ≠ 0 := hmaps hy
  simp only [Function.comp_apply]
  rw [dif_pos hdet]
  congr 1
  ext i j
  rfl

private theorem differentiableAt_torusFn (G : ℝ → ℂ) (hG : ContDiffOn ℝ 2 G (Set.Ioi 0)) :
    DifferentiableOn ℝ G (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv G) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y → DifferentiableAt ℝ G y) ∧
      (∀ y : ℝ, 0 < y → DifferentiableAt ℝ (deriv G) y) := by
  have h1 : DifferentiableOn ℝ G (Set.Ioi 0) := hG.differentiableOn (by simp)
  have h2 : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) :=
    (hG.deriv_of_isOpen isOpen_Ioi (le_of_eq one_add_one_eq_two)).differentiableOn one_ne_zero
  exact ⟨h1, h2, fun y hy => h1.differentiableAt (isOpen_Ioi.mem_nhds hy),
    fun y hy => h2.differentiableAt (isOpen_Ioi.mem_nhds hy)⟩

private theorem delta_statement (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (ν : ℂ)
    (hF : ContDiffOn ℝ 2
      (fun e : Fin 2 → Fin 2 → ℝ =>
        F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0})
    (hψ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ),
      F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    (hΩ : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => F (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * F m) :
    (DifferentiableOn ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (splitTorusGL2 (Real.log y / 2)) = 0) ∧
    (DifferentiableOn ℝ (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) = 0) := by

  have hψ1 : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * π * Complex.I * ((1 : ℝ) * x : ℝ)) * F m := by
    intro x m; rw [one_mul]; exact hψ x m
  have hreg := contDiffOn_torusFn F hF 1
  have hreg1 : ContDiffOn ℝ 2 (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) :=
    hreg.congr fun y _ => by rw [one_mul]
  obtain ⟨hd, hd', hda, hda'⟩ := differentiableAt_torusFn _ hreg1

  have hψJ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ), (fun m => F (UpperHalfPlane.J * m)) (unipotentGL2 x * m)
      = Complex.exp (2 * π * Complex.I * ((-1 : ℝ) * x : ℝ)) * (fun m => F (UpperHalfPlane.J * m)) m := by
    intro x m
    show F (UpperHalfPlane.J * (unipotentGL2 x * m)) = _ * F (UpperHalfPlane.J * m)
    rw [← mul_assoc, J_mul_unipotentGL2, mul_assoc, hψ, neg_one_mul]
  have hkJ : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), (fun m => F (UpperHalfPlane.J * m)) (m * k)
      = (archWeightCharℝ k₀ k : ℂ) * (fun m => F (UpperHalfPlane.J * m)) m := by
    intro k m
    show F (UpperHalfPlane.J * (m * k)) = _ * F (UpperHalfPlane.J * m)
    rw [← mul_assoc, hk]
  have hΩJ : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            (fun m => F (UpperHalfPlane.J * m)) (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ)
            * deriv (fun t : ℝ => (fun m => F (UpperHalfPlane.J * m)) (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            (fun m => F (UpperHalfPlane.J * m)) (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * (fun m => F (UpperHalfPlane.J * m)) m := by
    intro m
    have h := hΩ (UpperHalfPlane.J * m)
    simp only [mul_assoc] at h ⊢
    exact h
  have hregJ := contDiffOn_torusFn F hF UpperHalfPlane.J
  obtain ⟨hdJ, hdJ', hdaJ, hdaJ'⟩ := differentiableAt_torusFn _ hregJ
  refine ⟨⟨hd, hd', fun y hy => ?_⟩, ⟨hdJ, hdJ', fun y hy => ?_⟩⟩
  · have h := torus_ode F k₀ ν 1 hψ1 hk hΩ hda hda' hy
    push_cast at h ⊢
    linear_combination h
  · have h := torus_ode (fun m => F (UpperHalfPlane.J * m)) k₀ ν (-1) hψJ hkJ hΩJ hdaJ hdaJ' hy
    push_cast at h ⊢
    linear_combination h

section Adelic

open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

private theorem symm_mem_subgroup₀ {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

omit [NumberField K] in

private theorem archWeightCharAt_symm {w : InfinitePlace K} (hw : w.IsReal) (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    archWeightCharAt hw n ⟨_, symm_mem_subgroup₀ hw k⟩ = archWeightCharℝ n k := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      ⟨_, symm_mem_subgroup₀ hw k⟩ = k := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply, hmap]

private theorem archRealGLAt_eq_adelicArchGLInclAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

private theorem archDerivAt_archRealGLAt_mul {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) {g : AdelicGL2 (𝓞 K) K} (hg : AdelicLevel.glArch (𝓞 K) K g = 1)
    (m : GL (Fin 2) ℝ) :
    archDerivAt hw d φ (archRealGLAt hw m * g)
      = deriv (fun t : ℝ => φ (archRealGLAt hw (m * archFlowMatrix d t) * g)) 0 := by
  have hc : ∀ m' : GL (Fin 2) ℝ, archRealGLAt hw m' * g = g * archRealGLAt hw m' :=
    fun m' => archRealGLAt_mul_comm_of_glArch_eq_one hw m' hg
  simp only [archDerivAt, archFlowAt, map_mul, mul_assoc]
  simp only [hc]

end Adelic

section

open NumberField

theorem solution
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (W : AdelicGL2 (𝓞 K) K → ℂ)
    (k₀ : ℤ) (ν : ℂ)
    (hsm : IsArchSmoothAt hw W)
    (hΩ : archCasimirAt hw W = (1 / 4 - ν ^ 2) • W)
    (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw k₀) W)
    (hψ : ∀ (x : ℝ) (g : AdelicGL2 (𝓞 K) K),
      W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g)
    (g : AdelicGL2 (𝓞 K) K) (hg : AdelicLevel.glArch (𝓞 K) K g = 1) :
    (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
    (DifferentiableOn ℝ
        (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ
        (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv
              (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0) := by
  have hcomm : ∀ m : GL (Fin 2) ℝ, archRealGLAt hw m * g = g * archRealGLAt hw m :=
    fun m => archRealGLAt_mul_comm_of_glArch_eq_one hw m hg
  set Fg : GL (Fin 2) ℝ → ℂ := fun m => W (archRealGLAt hw m * g) with hFg

  have hF : ContDiffOn ℝ 2
      (fun e : Fin 2 → Fin 2 → ℝ =>
        Fg (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h else 1))
      {e | (Matrix.of e).det ≠ 0} := by
    have h2 : ContDiffOn ℝ 2 (fun e : Fin 2 → Fin 2 → ℝ => W (g * archRealLiftAt hw e))
        {e | (Matrix.of e).det ≠ 0} := by
      simpa using contDiffOn_infty.mp (hsm g) 2
    refine h2.congr fun e he => ?_
    have he' : (Matrix.of e).det ≠ 0 := he
    simp only [hFg, dif_pos he', archRealLiftAt_of_det_ne_zero hw he', hcomm]
  have hψ' : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      Fg (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * Fg m := by
    intro x m
    simp only [hFg]
    rw [map_mul, mul_assoc (archRealGLAt hw (unipotentGL2 x)) (archRealGLAt hw m) g]
    exact hψ x _
  have hk' : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), Fg (m * k) = (archWeightCharℝ k₀ k : ℂ) * Fg m := by
    intro k m
    have h := hk ⟨_, symm_mem_subgroup₀ hw k⟩ (archRealGLAt hw m * g)
    rw [archWeightCharAt_symm] at h
    simp only [hFg]
    rw [map_mul, mul_assoc (archRealGLAt hw m) (archRealGLAt hw (k : GL (Fin 2) ℝ)) g, hcomm (k : GL (Fin 2) ℝ),
      ← mul_assoc, archRealGLAt_eq_adelicArchGLInclAt hw (k : GL (Fin 2) ℝ)]
    exact h
  have hΩ' : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            Fg (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => Fg (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            Fg (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * Fg m := by
    intro m
    have h := congr_fun hΩ (archRealGLAt hw m * g)
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      archDerivAt_archRealGLAt_mul hw _ _ hg] at h
    simp only [hFg]
    exact h
  have h := delta_statement Fg k₀ ν hF hψ' hk' hΩ'
  simp only [hFg] at h
  exact h

end

end

end S_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
end P2MW
export P2MW.S_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq (solution)
