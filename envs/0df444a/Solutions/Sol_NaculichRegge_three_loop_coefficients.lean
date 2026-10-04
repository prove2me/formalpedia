-- Prove2me | solution 1 for NaculichRegge.three_loop_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:16:04.479994+00:00
-- url     : https://prove2.me/submissions/ac9a8bd2-e62f-4016-baea-d66a2bf9adee

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

open Polynomial NaculichRegge in
lemma P7a_Tt2_mulVec (v : Fin 6 → ℂ[X]) :
    Tt2.mulVec v = ![X * v 0 - v 5, 2 * (X * v 1) + v 3 + v 5, X * v 2 - v 3,
      2 * v 1 + 2 * (X * v 3), -(2 * v 0) - 2 * v 2, 2 * v 1 + 2 * (X * v 5)] := by
  funext i
  fin_cases i <;> simp [Tt2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
lemma P7a_Tsu2_mulVec (v : Fin 6 → ℂ[X]) :
    Tsu2.mulVec v = ![-(C (1 / 2) * (X * v 0)) - v 4 - C (1 / 2) * v 5,
      -(C (1 / 2) * v 3) + C (1 / 2) * v 5,
      C (1 / 2) * (X * v 2) + C (1 / 2) * v 3 + v 4,
      v 1 + 2 * v 2 + X * v 3, -v 0 + v 2, -(2 * v 0) - v 1 - X * v 5] := by
  funext i
  fin_cases i <;> simp [Tsu2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial in
lemma P7a_coeff_X_mul (p : ℂ[X]) (n : ℕ) :
    (X * p).coeff n = if n = 0 then 0 else p.coeff (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul]

open NaculichRegge in
lemma P7a_slot1 : extSlot 1 = 0 := by decide

open NaculichRegge in
lemma P7a_slot2 : extSlot 2 = 1 := by decide

open NaculichRegge in
lemma P7a_slot3 : extSlot 3 = 2 := by decide

open NaculichRegge in
lemma P7a_slot4 : extSlot 4 = 3 := by decide

open NaculichRegge in
lemma P7a_slot5 : extSlot 5 = 4 := by decide

open NaculichRegge in
lemma P7a_slot6 : extSlot 6 = 5 := by decide

open NaculichRegge in
lemma P7a_slot7 : extSlot 7 = 0 := by decide

open NaculichRegge in
lemma P7a_slot8 : extSlot 8 = 1 := by decide

open NaculichRegge in
lemma P7a_slot9 : extSlot 9 = 2 := by decide

open NaculichRegge in
lemma P7a_slot10 : extSlot 10 = 3 := by decide

open NaculichRegge in
lemma P7a_slot11 : extSlot 11 = 4 := by decide

open NaculichRegge in
lemma P7a_slot12 : extSlot 12 = 5 := by decide

open Polynomial in
lemma P7a_coeff_mul_two (p : ℂ[X]) (n : ℕ) : (p * 2).coeff n = p.coeff n * 2 := by
  rw [mul_comm, coeff_ofNat_mul, mul_comm]

open Polynomial NaculichRegge in
lemma P7a_index : reggeIndex 3 = {(0,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)} := by
  decide

open Polynomial NaculichRegge in
lemma P7a_coord1 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 1 = (1 : ℂ) * B (0, 0) + (-1/2 : ℂ) * B (1, 1) + (1/4 : ℂ) * B (2, 2) + (-1/8 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord3 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 3 = (-1 : ℂ) * B (0, 0) + (-1/2 : ℂ) * B (1, 1) + (-1/4 : ℂ) * B (2, 2) + (-1/8 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord4 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 4 = (-2 : ℂ) * B (1, 1) + (-2 : ℂ) * B (2, 1) + (-3 : ℂ) * B (2, 2) + (-2 : ℂ) * B (3, 1) + (-1 : ℂ) * B (3, 2) + (-7/2 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord6 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 6 = (-2 : ℂ) * B (1, 1) + (-2 : ℂ) * B (2, 1) + (3 : ℂ) * B (2, 2) + (-2 : ℂ) * B (3, 1) + (1 : ℂ) * B (3, 2) + (-7/2 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord7 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 7 = (2 : ℂ) * B (2, 1) + (3 : ℂ) * B (2, 2) + (2 : ℂ) * B (3, 1) + (-5 : ℂ) * B (3, 2) + (-3 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord8 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 8 = (-4 : ℂ) * B (2, 1) + (-8 : ℂ) * B (3, 1) + (3 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
lemma P7a_coord9 (B : ℕ × ℕ → ℂ) :
    extCoord 3 (reggeAmplitude 3 B) 9 = (2 : ℂ) * B (2, 1) + (-3 : ℂ) * B (2, 2) + (2 : ℂ) * B (3, 1) + (5 : ℂ) * B (3, 2) + (-3 : ℂ) * B (3, 3) := by
  simp only [extCoord, reggeAmplitude, P7a_index]
  simp [Finset.sum_insert, P7a_slot1, P7a_slot3, P7a_slot4, P7a_slot6, P7a_slot7, P7a_slot8, P7a_slot9, P7a_coeff_mul_two, extDegree, reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, pow_succ, P7a_Tt2_mulVec, P7a_Tsu2_mulVec, C00, P7a_coeff_X_mul, coeff_X_pow_mul', mul_assoc, coeff_C_mul, coeff_one, coeff_X] <;> ring

open Polynomial NaculichRegge in
theorem solution (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    κ * B (0, 0) = 1/2 * (colorOrderedAmp 3 κ B 1 - colorOrderedAmp 3 κ B 3)
        + 5/144 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        - 1/144 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (1, 1) = -13/12 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        + 1/48 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        + 1/48 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9) ∧
    κ * B (2, 1) = 3/4 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        - 3/16 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        + 5/16 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9)
        + 1/4 * colorOrderedAmp 3 κ B 8 ∧
    κ * B (2, 2) = -5/36 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        + 1/36 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (3, 1) = -1/4 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        + 1/16 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        - 3/16 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9)
        - 1/4 * colorOrderedAmp 3 κ B 8 ∧
    κ * B (3, 2) = -1/12 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        - 1/12 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (3, 3) = 1/3 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        - 1/12 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        - 1/12 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9) := by
  simp only [colorOrderedAmp, P7a_coord1, P7a_coord3, P7a_coord4, P7a_coord6, P7a_coord7,
    P7a_coord8, P7a_coord9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
