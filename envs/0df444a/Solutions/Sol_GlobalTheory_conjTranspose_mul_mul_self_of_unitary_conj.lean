-- Prove2me | solution 1 for GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:48.239153+00:00
-- url     : https://prove2.me/submissions/a62f71f5-f30e-4f7b-9d80-a76af00fd7e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open Matrix
open GlobalTheory
open scoped ComplexOrder
open Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel
end _root_.GlobalTheory
end GlobalTheory
