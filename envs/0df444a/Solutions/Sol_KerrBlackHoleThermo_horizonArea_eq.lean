-- Prove2me | solution 1 for KerrBlackHoleThermo.horizonArea_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:17:19.064992+00:00
-- url     : https://prove2.me/submissions/673856ff-a82b-46ed-87ec-0042ce0b945a

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

set_option autoImplicit false

open Real

open KerrBlackHoleThermo in
theorem kerrP2M_rPlus_sq_add (M a : ℝ) (ha : a ^ 2 ≤ M ^ 2) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * (M + √(M ^ 2 - a ^ 2)) := by
  have hs2 : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  unfold rPlus
  linear_combination hs2

open KerrBlackHoleThermo in
theorem kerrP2M_horizonArea_eq (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    horizonArea M a = 8 * π * M * (M + √(M ^ 2 - a ^ 2)) := by
  have hs0 : 0 ≤ √(M ^ 2 - a ^ 2) := Real.sqrt_nonneg _
  have hs2 : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  have hrpos : 0 < rPlus M a := by unfold rPlus; linarith
  have hdelta : kerrDelta M a (rPlus M a) = 0 := by
    unfold kerrDelta rPlus; linear_combination hs2
  have hpt : ∀ θ : ℝ, √(gThetaTheta a (rPlus M a) θ * gPhiPhi M a (rPlus M a) θ)
      = |(rPlus M a ^ 2 + a ^ 2) * sin θ| := by
    intro θ
    have hS : 0 < kerrSigma a (rPlus M a) θ := by
      unfold kerrSigma; positivity
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    unfold gThetaTheta gPhiPhi
    rw [hdelta]
    field_simp
    ring
  have key : Set.EqOn
      (fun θ => ∫ _φ in (0:ℝ)..(2 * π),
        √(gThetaTheta a (rPlus M a) θ * gPhiPhi M a (rPlus M a) θ))
      (fun θ => (2 * π * (rPlus M a ^ 2 + a ^ 2)) * sin θ) (Set.uIcc 0 π) := by
    intro θ hθ
    rw [Set.uIcc_of_le pi_pos.le] at hθ
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [hpt θ, abs_of_nonneg (mul_nonneg (by positivity) hsin)]
    ring
  unfold horizonArea
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_const_mul, integral_sin,
    cos_pi, cos_zero, kerrP2M_rPlus_sq_add M a ha]
  ring

open KerrBlackHoleThermo Real in
theorem solution (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    horizonArea M a = 8 * π * M * (M + √(M ^ 2 - a ^ 2)) := by
  exact kerrP2M_horizonArea_eq M a hM ha
