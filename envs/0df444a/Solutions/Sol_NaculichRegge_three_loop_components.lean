-- Prove2me | solution 1 for NaculichRegge.three_loop_components
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T16:59:30.229264+00:00
-- url     : https://prove2.me/submissions/d47a9f40-674c-4eb2-9d7c-8279c31cb6b3

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

open Polynomial NaculichRegge in
lemma a756_Tt2_mulVec (a b c d e f : ℂ[X]) :
    Matrix.mulVec Tt2 ![a, b, c, d, e, f] =
      ![X * a - f, 2 * X * b + d + f, X * c - d, 2 * b + 2 * X * d, -2 * a - 2 * c,
        2 * b + 2 * X * f] := by
  funext i
  fin_cases i <;> simp [Tt2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
lemma a756_Tsu2_mulVec (a b c d e f : ℂ[X]) :
    Matrix.mulVec Tsu2 ![a, b, c, d, e, f] =
      ![-(C (1 / 2) * X) * a - e - C (1 / 2) * f, -C (1 / 2) * d + C (1 / 2) * f,
        C (1 / 2) * X * c + C (1 / 2) * d + e, b + 2 * c + X * d, -a + c, -2 * a - b - X * f] := by
  funext i
  fin_cases i <;> simp [Tsu2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
lemma a756_comm_mulVec (A B : ColorOp) (v : ColorVec) :
    Matrix.mulVec (NaculichRegge.comm A B) v =
      Matrix.mulVec A (Matrix.mulVec B v) - Matrix.mulVec B (Matrix.mulVec A v) := by
  simp [NaculichRegge.comm, Matrix.sub_mulVec, Matrix.mulVec_mulVec]

open Polynomial NaculichRegge in
lemma a756_C00 : C00 = ![(1 : ℂ[X]), 0, -1, 0, 0, 0] := rfl

open Polynomial NaculichRegge in
lemma a756_vec_sub (a b c d e f a' b' c' d' e' f' : ℂ[X]) :
    ![a, b, c, d, e, f] - ![a', b', c', d', e', f'] =
      ![a - a', b - b', c - c', d - d', e - e', f - f'] := by
  funext i; fin_cases i <;> rfl

open Polynomial NaculichRegge in
lemma a756_vec_smul (p a b c d e f : ℂ[X]) :
    p • ![a, b, c, d, e, f] = ![p * a, p * b, p * c, p * d, p * e, p * f] := by
  funext i; fin_cases i <;> rfl

open Polynomial NaculichRegge in
lemma a756_C31 : reggeColor 3 1 =
    ![2 * X, -8 * X, 2 * X, -8 - 2 * X ^ 2, -8 - 4 * X ^ 2, -8 - 2 * X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    a756_comm_mulVec, a756_C00, a756_Tt2_mulVec, a756_Tsu2_mulVec, a756_vec_sub]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_list (p0 p1 p2 p3 p4 p5 : ℂ[X]) :
    (List.range 12).map (fun m => extCoord 3 ![p0, p1, p2, p3, p4, p5] (m + 1)) =
      [p0.coeff 3, p1.coeff 3, p2.coeff 3, p3.coeff 2, p4.coeff 2, p5.coeff 2,
       p0.coeff 1, p1.coeff 1, p2.coeff 1, p3.coeff 0, p4.coeff 0, p5.coeff 0] := by
  simp [List.range_succ, extCoord, extSlot, extDegree]

open Polynomial NaculichRegge in
lemma a756_A0 : (X : ℂ[X]) ^ 3 • reggeColor 0 0 = ![X ^ 3, 0, -X ^ 3, 0, 0, 0] := by
  simp only [reggeColor, reggeOp, if_true, Matrix.one_mulVec, a756_C00, a756_vec_smul]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_A1 : (X : ℂ[X]) ^ 2 • reggeColor 1 1 =
    ![C (-1/2) * X ^ 3, 0, C (-1/2) * X ^ 3, C (-2) * X ^ 2, C (-2) * X ^ 2, C (-2) * X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [a756_C00, a756_Tsu2_mulVec, a756_vec_smul]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_A2 : (X : ℂ[X]) • reggeColor 2 1 =
    ![2 * X, -4 * X, 2 * X, -2 * X ^ 2, 4 * X ^ 2, -2 * X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    a756_comm_mulVec, a756_C00, a756_Tt2_mulVec, a756_Tsu2_mulVec, a756_vec_sub, a756_vec_smul]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_A3 : (X : ℂ[X]) • reggeColor 2 2 =
    ![3 * X + C (1/4) * X ^ 3, 0, -3 * X - C (1/4) * X ^ 3, -3 * X ^ 2, 0, 3 * X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [pow_two, ← Matrix.mulVec_mulVec, a756_C00, a756_Tsu2_mulVec, a756_vec_smul]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_A5 : reggeColor 3 2 = ![-5 * X, 0, 5 * X, -X ^ 2, 0, X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    a756_comm_mulVec, a756_C00, a756_Tt2_mulVec, a756_Tsu2_mulVec, a756_vec_sub]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
lemma a756_A6 : reggeColor 3 3 =
    ![-3 * X - C (1/8) * X ^ 3, 3 * X, -3 * X - C (1/8) * X ^ 3, -6 - C (7/2) * X ^ 2,
      -6 - C (1/2) * X ^ 2, -6 - C (7/2) * X ^ 2] := by
  simp only [reggeColor, reggeOp]
  norm_num
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec, a756_C00,
    a756_Tsu2_mulVec]
  funext i
  fin_cases i <;> (apply Polynomial.funext; intro r; simp; try ring)

open Polynomial NaculichRegge in
theorem solution :
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) ^ 3 • reggeColor 0 0) (m + 1)) =
        [1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) ^ 2 • reggeColor 1 1) (m + 1)) =
        [-1/2, 0, -1/2, -2, -2, -2, 0, 0, 0, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) • reggeColor 2 1) (m + 1)) =
        [0, 0, 0, -2, 4, -2, 2, -4, 2, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) • reggeColor 2 2) (m + 1)) =
        [1/4, 0, -1/4, -3, 0, 3, 3, 0, -3, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 1) (m + 1)) =
        [0, 0, 0, -2, -4, -2, 2, -8, 2, -8, -8, -8] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 2) (m + 1)) =
        [0, 0, 0, -1, 0, 1, -5, 0, 5, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 3) (m + 1)) =
        [-1/8, 0, -1/8, -7/2, -1/2, -7/2, -3, 3, -3, -6, -6, -6] := by
  rw [a756_A0, a756_A1, a756_A2, a756_A3, a756_C31, a756_A5, a756_A6]
  simp only [a756_list]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_one] <;>
    norm_num
