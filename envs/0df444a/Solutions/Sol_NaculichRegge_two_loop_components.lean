-- Prove2me | solution 1 for NaculichRegge.two_loop_components
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:02:46.09934+00:00
-- url     : https://prove2.me/submissions/c566b377-92cd-4431-ac9b-006d8f1e026b

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

open Polynomial in
theorem a29bba6f_hC : (C (1 / 2 : ℂ)) * 2 = 1 := by
  rw [show (2 : ℂ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]
  norm_num

open Polynomial in
theorem a29bba6f_hC4 : (C (1 / 4 : ℂ)) = C (1 / 2 : ℂ) ^ 2 := by
  rw [← C_pow]; norm_num

open Polynomial NaculichRegge in
theorem a29bba6f_v11 : reggeColor 1 1 =
    ![-(C (1 / 2 : ℂ) * X), 0, -(C (1 / 2 : ℂ) * X), -2, -2, -2] := by
  have h : reggeColor 1 1 = Tsu2.mulVec C00 := by
    simp [reggeColor, reggeOp]
  rw [h]
  ext i : 1
  fin_cases i <;> simp [Tsu2, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
theorem a29bba6f_Ts (h : ℂ[X]) (hh : h = C (1 / 2 : ℂ)) : Tsu2 =
    !![-(h * X), 0, 0, 0, -1, -h;
       0, 0, 0, -h, 0, h;
       0, 0, h * X, h, 1, 0;
       0, 1, 2, X, 0, 0;
       -1, 0, 1, 0, 0, 0;
       -2, -1, 0, 0, 0, -X] := by
  subst hh
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

open Polynomial NaculichRegge in
theorem a29bba6f_v22 : reggeColor 2 2 =
    ![C (1 / 4 : ℂ) * X ^ 2 + 3, 0, -(C (1 / 4 : ℂ) * X ^ 2) - 3, -3 * X, 0, 3 * X] := by
  have hr : reggeColor 2 2 = Tsu2.mulVec (reggeColor 1 1) := by
    simp [reggeColor, reggeOp, pow_two, Matrix.mulVec_mulVec]
  obtain ⟨h, hh⟩ : ∃ h : ℂ[X], h = C (1 / 2 : ℂ) := ⟨_, rfl⟩
  have hC' : h * 2 = 1 := by rw [hh]; exact a29bba6f_hC
  rw [hr, a29bba6f_v11, a29bba6f_Ts h hh, a29bba6f_hC4, ← hh]
  ext i : 1
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals
    first
    | ring1
    | linear_combination hC'
    | linear_combination -hC'
    | linear_combination X * hC'
    | linear_combination -X * hC'
    | linear_combination 2 * X * hC'
    | linear_combination -2 * X * hC'
    | linear_combination 2 * hC'
    | linear_combination -2 * hC'

open Polynomial NaculichRegge in
theorem a29bba6f_v21 : reggeColor 2 1 = ![2, -4, 2, -2 * X, 4 * X, -2 * X] := by
  have h0 : Tt2.mulVec C00 = (X : ℂ[X]) • C00 := by
    ext i
    fin_cases i <;> simp [Tt2, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hr : reggeColor 2 1 = Tt2.mulVec (reggeColor 1 1) - (X : ℂ[X]) • reggeColor 1 1 := by
    have e : reggeColor 2 1 = (comm Tt2 Tsu2).mulVec C00 := by
      simp [reggeColor, reggeOp]
    rw [e]
    unfold NaculichRegge.comm
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0,
      Matrix.mulVec_smul]
    simp [reggeColor, reggeOp]
  obtain ⟨h, hh⟩ : ∃ h : ℂ[X], h = C (1 / 2 : ℂ) := ⟨_, rfl⟩
  have hC' : h * 2 = 1 := by rw [hh]; exact a29bba6f_hC
  rw [hr, a29bba6f_v11, ← hh]
  ext i : 1
  fin_cases i <;> simp [Tt2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals
    first
    | ring1
    | linear_combination hC'
    | linear_combination -hC'
    | linear_combination X * hC'
    | linear_combination -X * hC'
    | linear_combination 2 * X * hC'
    | linear_combination -2 * X * hC'
    | linear_combination 2 * hC'
    | linear_combination -2 * hC'

open Polynomial NaculichRegge in
theorem solution :
    (List.range 9).map (fun m => extCoord 2 ((X : ℂ[X]) ^ 2 • reggeColor 0 0) (m + 1)) =
        [1, 0, -1, 0, 0, 0, 0, 0, 0] ∧
    (List.range 9).map (fun m => extCoord 2 ((X : ℂ[X]) • reggeColor 1 1) (m + 1)) =
        [-1/2, 0, -1/2, -2, -2, -2, 0, 0, 0] ∧
    (List.range 9).map (fun m => extCoord 2 (reggeColor 2 1) (m + 1)) =
        [0, 0, 0, -2, 4, -2, 2, -4, 2] ∧
    (List.range 9).map (fun m => extCoord 2 (reggeColor 2 2) (m + 1)) =
        [1/4, 0, -1/4, -3, 0, 3, 3, 0, -3] := by
  have h00 : reggeColor 0 0 = C00 := by simp [reggeColor, reggeOp]
  rw [h00, a29bba6f_v11, a29bba6f_v21, a29bba6f_v22]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [List.range_succ, extCoord, extDegree, extSlot, C00, coeff_X, coeff_C, coeff_one,
      coeff_X_pow, coeff_C_mul, Polynomial.coeff_neg] <;> norm_num
