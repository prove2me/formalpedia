-- Prove2me | solution 1 for NaculichRegge.two_loop_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:02:46.054254+00:00
-- url     : https://prove2.me/submissions/6b5f0173-8631-4a55-aea8-5814f38e384f

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

open Polynomial NaculichRegge in
theorem nr2_idx : reggeIndex 2 = {(0,0),(1,1),(2,1),(2,2)} := by decide

open Polynomial NaculichRegge in
theorem nr2_C00 : reggeColor 0 0 = C00 := by
  simp [reggeColor, reggeOp]

open Polynomial NaculichRegge in
theorem nr2_C11 : reggeColor 1 1 =
    ![-(C (2⁻¹:ℂ) * X), 0, -(C (2⁻¹:ℂ) * X), -2, -2, -2] := by
  funext i
  fin_cases i <;> simp [reggeColor, reggeOp, Tsu2, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
theorem nr2_Tsu2C00 : Tsu2.mulVec C00 =
    ![-(C (2⁻¹:ℂ) * X), 0, -(C (2⁻¹:ℂ) * X), -2, -2, -2] := by
  have := nr2_C11
  simpa [reggeColor, reggeOp] using this

open Polynomial NaculichRegge in
theorem nr2_C22 : reggeColor 2 2 =
    ![C (2⁻¹:ℂ) * X * (C (2⁻¹:ℂ) * X) + 2 + 2 * C (2⁻¹:ℂ), 0,
      -(C (2⁻¹:ℂ) * X * (C (2⁻¹:ℂ) * X)) - 2 * C (2⁻¹:ℂ) - 2,
      -(2 * C (2⁻¹:ℂ) * X) - 2 * X, 0, 2 * C (2⁻¹:ℂ) * X + 2 * X] := by
  have h : reggeColor 2 2 = Tsu2.mulVec (Tsu2.mulVec C00) := by
    simp [reggeColor, reggeOp, sq, Matrix.mulVec_mulVec]
  rw [h, nr2_Tsu2C00]
  funext i
  fin_cases i <;> simp [Tsu2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open Polynomial NaculichRegge in
theorem nr2_C21 : reggeColor 2 1 = ![2, -4, 2, -(2 * X), 4 * X, -(2 * X)] := by
  have h : reggeColor 2 1 = Tt2.mulVec (Tsu2.mulVec C00) - Tsu2.mulVec (Tt2.mulVec C00) := by
    simp [reggeColor, reggeOp, NaculichRegge.comm, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have h2 : Tt2.mulVec C00 = ![X, 0, -X, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [Tt2, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [h, h2, nr2_Tsu2C00]
  have hh : (C (2⁻¹:ℂ) : ℂ[X]) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  funext i
  fin_cases i <;> simp [Tt2, Tsu2] <;>
    first | ring1 | linear_combination (2 * X) * hh

open Polynomial NaculichRegge in
theorem nr2_hh : (C (2⁻¹:ℂ) : ℂ[X]) * 2 = 1 := by
  rw [← map_ofNat C 2, ← C_mul]; norm_num

open Polynomial NaculichRegge in
theorem nr2_amp (B : ℕ × ℕ → ℂ) : reggeAmplitude 2 B =
    (C (B (0,0)) * X ^ 2) • C00 + (C (B (1,1)) * X) • reggeColor 1 1 +
      C (B (2,1)) • reggeColor 2 1 + C (B (2,2)) • reggeColor 2 2 := by
  rw [reggeAmplitude, nr2_idx]
  simp [Finset.sum_insert, nr2_C00]
  abel

open Polynomial NaculichRegge in
theorem nr2_slot0 (B : ℕ × ℕ → ℂ) : reggeAmplitude 2 B 0 =
    C (B (0,0) - B (1,1) * (1/2) + B (2,2) * (1/2) ^ 2) * X ^ 2 + C (2 * B (2,1) + 3 * B (2,2)) := by
  rw [nr2_amp, nr2_C11, nr2_C21, nr2_C22]
  have e2 : (C (2:ℂ) : ℂ[X]) = 2 := map_ofNat C 2
  have e3 : (C (3:ℂ) : ℂ[X]) = 3 := map_ofNat C 3
  have e4 : (C ((2:ℂ) ^ 2)⁻¹ : ℂ[X]) = C (2⁻¹ : ℂ) ^ 2 := by rw [← map_pow, inv_pow]
  simp [C00, e2, e3, e4]
  linear_combination (C (B (2,2))) * nr2_hh

open Polynomial NaculichRegge in
theorem nr2_slot2 (B : ℕ × ℕ → ℂ) : reggeAmplitude 2 B 2 =
    C (-B (0,0) - B (1,1) * (1/2) - B (2,2) * (1/2) ^ 2) * X ^ 2 + C (2 * B (2,1) - 3 * B (2,2)) := by
  rw [nr2_amp, nr2_C11, nr2_C21, nr2_C22]
  have e2 : (C (2:ℂ) : ℂ[X]) = 2 := map_ofNat C 2
  have e3 : (C (3:ℂ) : ℂ[X]) = 3 := map_ofNat C 3
  have e4 : (C ((2:ℂ) ^ 2)⁻¹ : ℂ[X]) = C (2⁻¹ : ℂ) ^ 2 := by rw [← map_pow, inv_pow]
  simp [C00, e2, e3, e4]
  linear_combination (-C (B (2,2))) * nr2_hh

open Polynomial NaculichRegge in
theorem nr2_A (κ : ℂ) (B : ℕ × ℕ → ℂ) (lam : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ 9) :
    colorOrderedAmp 2 κ B lam = κ * (reggeAmplitude 2 B (extSlot lam)).coeff (extDegree 2 lam) := by
  have h : 1 ≤ lam ∧ lam ≤ 3 * 2 + 3 := ⟨h1, by omega⟩
  simp only [colorOrderedAmp, extCoord, if_pos h]

open Polynomial NaculichRegge in
theorem nr2_A1 (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    colorOrderedAmp 2 κ B 1 = κ * (B (0,0) - B (1,1) * (1/2) + B (2,2) * (1/2) ^ 2) := by
  rw [nr2_A κ B 1 (by norm_num) (by norm_num), show extSlot 1 = 0 by decide,
    show extDegree 2 1 = 2 by decide, nr2_slot0]
  rw [coeff_add, coeff_C_mul_X_pow, coeff_C]
  simp

open Polynomial NaculichRegge in
theorem nr2_A3 (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    colorOrderedAmp 2 κ B 3 = κ * (-B (0,0) - B (1,1) * (1/2) - B (2,2) * (1/2) ^ 2) := by
  rw [nr2_A κ B 3 (by norm_num) (by norm_num), show extSlot 3 = 2 by decide,
    show extDegree 2 3 = 2 by decide, nr2_slot2]
  rw [coeff_add, coeff_C_mul_X_pow, coeff_C]
  simp

open Polynomial NaculichRegge in
theorem nr2_A7 (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    colorOrderedAmp 2 κ B 7 = κ * (2 * B (2,1) + 3 * B (2,2)) := by
  rw [nr2_A κ B 7 (by norm_num) (by norm_num), show extSlot 7 = 0 by decide,
    show extDegree 2 7 = 0 by decide, nr2_slot0]
  rw [coeff_add, coeff_C_mul_X_pow, coeff_C]
  simp

open Polynomial NaculichRegge in
theorem nr2_A9 (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    colorOrderedAmp 2 κ B 9 = κ * (2 * B (2,1) - 3 * B (2,2)) := by
  rw [nr2_A κ B 9 (by norm_num) (by norm_num), show extSlot 9 = 2 by decide,
    show extDegree 2 9 = 0 by decide, nr2_slot2]
  rw [coeff_add, coeff_C_mul_X_pow, coeff_C]
  simp

open Polynomial NaculichRegge in
theorem solution (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    κ * B (0, 0) = 1/2 * (colorOrderedAmp 2 κ B 1 - colorOrderedAmp 2 κ B 3)
        - 1/24 * (colorOrderedAmp 2 κ B 7 - colorOrderedAmp 2 κ B 9) ∧
    κ * B (1, 1) = -(colorOrderedAmp 2 κ B 1 + colorOrderedAmp 2 κ B 3) ∧
    κ * B (2, 1) = 1/4 * (colorOrderedAmp 2 κ B 7 + colorOrderedAmp 2 κ B 9) ∧
    κ * B (2, 2) = 1/6 * (colorOrderedAmp 2 κ B 7 - colorOrderedAmp 2 κ B 9) := by
  rw [nr2_A1, nr2_A3, nr2_A7, nr2_A9]
  refine ⟨by ring, by ring, by ring, by ring⟩
