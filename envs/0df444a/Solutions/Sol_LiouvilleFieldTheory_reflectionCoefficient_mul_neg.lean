-- Prove2me | solution 1 for LiouvilleFieldTheory.reflectionCoefficient_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:33:08.712046+00:00
-- url     : https://prove2.me/submissions/38ca2b3f-00c1-44f7-98e8-aaa87ab45caf

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics

open Complex in
theorem aadd88e7_sign_sq (b : ℂ) :
    LiouvilleFieldTheory.reflectionSign b * LiouvilleFieldTheory.reflectionSign b = 1 := by
  unfold LiouvilleFieldTheory.reflectionSign
  split_ifs <;> norm_num

open Complex in
theorem aadd88e7_gamma_ne (x : ℂ) (h : ∀ n : ℤ, x ≠ n) : Gamma x ≠ 0 ∧ Gamma (-x) ≠ 0 := by
  constructor
  · apply Complex.Gamma_ne_zero
    intro m hm
    exact h (-(m : ℤ)) (by rw [hm]; push_cast; ring)
  · apply Complex.Gamma_ne_zero
    intro m hm
    exact h (m : ℤ) (by have := congrArg Neg.neg hm; simp at this; rw [this]; push_cast; ring)

open Complex in
theorem aadd88e7_main (b lam P : ℂ) (hlam : lam ≠ 0)
    (hP : ∀ n : ℤ, 2 * I * b * P ≠ n ∧ 2 * I * b⁻¹ * P ≠ n) :
    LiouvilleFieldTheory.reflectionCoefficient b lam P *
      LiouvilleFieldTheory.reflectionCoefficient b lam (-P) = 1 := by
  unfold LiouvilleFieldTheory.reflectionCoefficient
  obtain ⟨h1, h2⟩ := aadd88e7_gamma_ne (2 * I * b * P) (fun n => (hP n).1)
  obtain ⟨h3, h4⟩ := aadd88e7_gamma_ne (2 * I * b⁻¹ * P) (fun n => (hP n).2)
  have e1 : 2 * I * b * -P = -(2 * I * b * P) := by ring
  have e2 : 2 * I * b⁻¹ * -P = -(2 * I * b⁻¹ * P) := by ring
  have e3 : -2 * I * b * -P = 2 * I * b * P := by ring
  have e4 : -2 * I * b⁻¹ * -P = 2 * I * b⁻¹ * P := by ring
  have e5 : -2 * I * b * P = -(2 * I * b * P) := by ring
  have e6 : -2 * I * b⁻¹ * P = -(2 * I * b⁻¹ * P) := by ring
  have e7 : -2 * I * -P = -(-2 * I * P) := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, Complex.cpow_neg]
  have hc : lam ^ (-2 * I * P) ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
    (by intro h; have := (hP 0).1; simp_all) ).mpr hlam
  have hs := aadd88e7_sign_sq b
  generalize LiouvilleFieldTheory.reflectionSign b = s at hs ⊢
  generalize lam ^ (-2 * I * P) = A at hc ⊢
  generalize Gamma (2 * I * b * P) = G1 at h1 ⊢
  generalize Gamma (2 * I * b⁻¹ * P) = G2 at h3 ⊢
  generalize Gamma (-(2 * I * b * P)) = G3 at h2 ⊢
  generalize Gamma (-(2 * I * b⁻¹ * P)) = G4 at h4 ⊢
  have k1 : G1 * G2 ≠ 0 := mul_ne_zero h1 h3
  have k2 : G3 * G4 ≠ 0 := mul_ne_zero h2 h4
  calc s * A * (G1 * G2) / (G3 * G4) * (s * A⁻¹ * (G3 * G4) / (G1 * G2))
      = (s * s) * (A * A⁻¹) * ((G1 * G2) / (G1 * G2)) * ((G3 * G4) / (G3 * G4)) := by ring
    _ = 1 := by rw [hs, mul_inv_cancel₀ hc, div_self k1, div_self k2]; ring

open Complex LiouvilleFieldTheory in
theorem solution (b lam P : ℂ) (hlam : lam ≠ 0)
    (hP : ∀ n : ℤ, 2 * I * b * P ≠ n ∧ 2 * I * b⁻¹ * P ≠ n) :
    reflectionCoefficient b lam P * reflectionCoefficient b lam (-P) = 1 := by
  exact aadd88e7_main b lam P hlam hP
