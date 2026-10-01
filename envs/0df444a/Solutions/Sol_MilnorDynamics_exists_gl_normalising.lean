-- Prove2me | solution 1 for MilnorDynamics.exists_gl_normalising
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T03:04:00.980978+00:00
-- url     : https://prove2.me/submissions/fdff91d3-fe79-4565-96b9-cdb595152e63

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Three distinct points of the Riemann sphere are carried to `0`, `1` and `∞` by a single
invertible complex `2 × 2` matrix.  Each case reduces the explicit matrix entries before doing
the rational arithmetic. -/
theorem solution (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℂ,
      g • a = ((0 : ℂ) : OnePoint ℂ) ∧ g • b = ((1 : ℂ) : OnePoint ℂ) ∧ g • c = ∞ := by
  classical
  have hcoe : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (h : Matrix.det A ≠ 0),
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = A := fun A h => rfl
  cases a with
  | infty =>
    cases b with
    | infty => exact absurd rfl hab
    | coe b =>
      cases c with
      | infty => exact absurd rfl hac
      | coe c =>
        have hbc' : b ≠ c := fun h => hbc (by rw [h])
        have e00 : (!![0, b - c; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by simp
        have e01 : (!![0, b - c; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b - c := by simp
        have e10 : (!![0, b - c; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by simp
        have e11 : (!![0, b - c; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -c := by simp
        refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, b - c; 1, -c] (by
          rw [Matrix.det_fin_two_of]
          intro h
          exact neg_ne_zero.mpr (sub_ne_zero.mpr hbc') (by linear_combination h)), ?_, ?_, ?_⟩
        · rw [OnePoint.smul_infty_eq_ite, hcoe, e10]
          simp
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (sub_eq_zero.mp (by linear_combination h)) hbc'
          · rw [OnePoint.coe_eq_coe]
            rw [div_eq_iff (show (1 : ℂ) * b + -c ≠ 0 from
              fun hh => hbc' (sub_eq_zero.mp (by linear_combination hh)))]
            ring
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · rfl
          · exact absurd (by ring : (1 : ℂ) * c + -c = 0) h
  | coe a =>
    cases b with
    | infty =>
      cases c with
      | infty => exact absurd rfl hbc
      | coe c =>
        have hac' : a ≠ c := fun h => hac (by rw [h])
        have e00 : (!![1, -a; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by simp
        have e01 : (!![1, -a; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -a := by simp
        have e10 : (!![1, -a; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by simp
        have e11 : (!![1, -a; 1, -c] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -c := by simp
        refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -a; 1, -c] (by
          rw [Matrix.det_fin_two_of]
          intro h
          exact sub_ne_zero.mpr hac' (by linear_combination h)), ?_, ?_, ?_⟩
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (sub_eq_zero.mp (by linear_combination h)) hac'
          · rw [OnePoint.coe_eq_coe]
            field_simp
            ring
        · rw [OnePoint.smul_infty_eq_ite, hcoe, e10]
          simp
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · rfl
          · exact absurd (by ring : (1 : ℂ) * c + -c = 0) h
    | coe b =>
      cases c with
      | infty =>
        have hba' : b ≠ a := fun h => hab (by rw [h])
        have e00 : (!![1, -a; 0, b - a] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by simp
        have e01 : (!![1, -a; 0, b - a] : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -a := by simp
        have e10 : (!![1, -a; 0, b - a] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by simp
        have e11 : (!![1, -a; 0, b - a] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = b - a := by simp
        refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -a; 0, b - a] (by
          rw [Matrix.det_fin_two_of]
          intro h
          exact sub_ne_zero.mpr hba' (by linear_combination h)), ?_, ?_, ?_⟩
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (sub_eq_zero.mp (by linear_combination h)) hba'
          · rw [OnePoint.coe_eq_coe]
            field_simp
            ring
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (sub_eq_zero.mp (by linear_combination h)) hba'
          · rw [OnePoint.coe_eq_coe]
            rw [div_eq_iff (show (0 : ℂ) * b + (b - a) ≠ 0 from
              fun hh => hba' (sub_eq_zero.mp (by linear_combination hh)))]
            ring
        · rw [OnePoint.smul_infty_eq_ite, hcoe, e10]
          simp
      | coe c =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        have hac' : a ≠ c := fun h => hac (by rw [h])
        have hbc' : b ≠ c := fun h => hbc (by rw [h])
        have hba' : b ≠ a := fun h => hab' h.symm
        have e00 : (!![b - c, -(b - c) * a; b - a, -(b - a) * c] :
            Matrix (Fin 2) (Fin 2) ℂ) 0 0 = b - c := by simp
        have e01 : (!![b - c, -(b - c) * a; b - a, -(b - a) * c] :
            Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -(b - c) * a := by simp
        have e10 : (!![b - c, -(b - c) * a; b - a, -(b - a) * c] :
            Matrix (Fin 2) (Fin 2) ℂ) 1 0 = b - a := by simp
        have e11 : (!![b - c, -(b - c) * a; b - a, -(b - a) * c] :
            Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -(b - a) * c := by simp
        refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![b - c, -(b - c) * a; b - a, -(b - a) * c] (by
          rw [Matrix.det_fin_two_of]
          intro h
          exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hbc') (sub_ne_zero.mpr hba'))
            (sub_ne_zero.mpr hac') (by linear_combination h)), ?_, ?_, ?_⟩
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (by linear_combination h)
              (mul_ne_zero (sub_ne_zero.mpr hba') (sub_ne_zero.mpr hac'))
          · rw [OnePoint.coe_eq_coe]
            rw [div_eq_iff (show (b - a) * a + -(b - a) * c ≠ 0 from
              fun hh => mul_ne_zero (sub_ne_zero.mpr hba') (sub_ne_zero.mpr hac')
                (by linear_combination hh))]
            ring
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · exact absurd (by linear_combination h)
              (mul_ne_zero (sub_ne_zero.mpr hba') (sub_ne_zero.mpr hbc'))
          · rw [OnePoint.coe_eq_coe]
            rw [div_eq_iff (show (b - a) * b + -(b - a) * c ≠ 0 from
              fun hh => mul_ne_zero (sub_ne_zero.mpr hba') (sub_ne_zero.mpr hbc')
                (by linear_combination hh))]
            ring
        · rw [OnePoint.smul_some_eq_ite, hcoe, e00, e01, e10, e11]
          split_ifs with h
          · rfl
          · exact absurd (by ring : (b - a) * c + -(b - a) * c = 0) h
