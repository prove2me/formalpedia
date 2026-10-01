-- Prove2me | solution 1 for KerrBlackHoleThermo.first_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:27:15.914987+00:00
-- url     : https://prove2.me/submissions/d9789879-6067-49f7-b0ef-c3d19748b0d4

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

set_option autoImplicit false

open Real

open KerrBlackHoleThermo in
theorem kerrFL_rPlus_sq_add (M a : ℝ) (ha : a ^ 2 ≤ M ^ 2) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * (M + √(M ^ 2 - a ^ 2)) := by
  have hs2 : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  unfold rPlus
  linear_combination hs2

open KerrBlackHoleThermo in
theorem kerrFL_horizonArea_eq (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
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
    cos_pi, cos_zero, kerrFL_rPlus_sq_add M a ha]
  ring

open KerrBlackHoleThermo in
theorem kerrFL_area_eq_on (p : ℝ × ℝ) (h1 : 0 < p.1) (h2 : p.2 ^ 2 < p.1 ^ 4) :
    horizonArea p.1 (p.2 / p.1) = 8 * π * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2)) := by
  have hle : (p.2 / p.1) ^ 2 ≤ p.1 ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith
  rw [kerrFL_horizonArea_eq _ _ h1 hle]
  have hfac : p.1 ^ 4 - p.2 ^ 2 = p.1 ^ 2 * (p.1 ^ 2 - (p.2 / p.1) ^ 2) := by
    field_simp
  rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1.le]
  ring

open KerrBlackHoleThermo Real in
theorem solution (M J : ℝ) (hM : 0 < M) (hJ : J ^ 2 < M ^ 4) :
    ∃ dA : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => horizonArea p.1 (p.2 / p.1)) dA (M, J) ∧
      ContinuousLinearMap.fst ℝ ℝ ℝ
        = (surfaceGravity M (J / M) / (8 * π)) • dA
          + horizonAngularVelocity M (J / M) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have hspos : 0 < M ^ 4 - J ^ 2 := by linarith
  set s := √(M ^ 4 - J ^ 2) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hspos
  have hs2 : s ^ 2 = M ^ 4 - J ^ 2 := Real.sq_sqrt hspos.le
  have hq : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ 4 - p.2 ^ 2)
      ((4 * M ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ - (2 * J) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (M, J) := by
    have := ((hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (M, J)).pow 4).sub
      ((hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (M, J)).pow 2)
    refine this.congr_fderiv ?_
    ext <;> (simp [nsmul_eq_mul]; try ring)
  have hsq := hq.sqrt (by simp; exact hspos.ne')
  have hg := (((hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (M, J)).pow 2).add hsq).const_mul (8 * π)
  have heq : (fun p : ℝ × ℝ => horizonArea p.1 (p.2 / p.1)) =ᶠ[nhds (M, J)]
      (fun p : ℝ × ℝ => 8 * π * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2))) := by
    have hopen : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ^ 2 < p.1 ^ 4} :=
      (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt (continuous_snd.pow 2) (continuous_fst.pow 4))
    filter_upwards [hopen.mem_nhds ⟨hM, hJ⟩] with p hp
    exact kerrFL_area_eq_on p hp.1 hp.2
  refine ⟨_, hg.congr_of_eventuallyEq heq, ?_⟩
  have hroot : √(M ^ 2 - (J / M) ^ 2) = s / M := by
    have : M ^ 2 - (J / M) ^ 2 = (s / M) ^ 2 := by
      rw [div_pow, div_pow, hs2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  unfold surfaceGravity horizonAngularVelocity
  rw [hroot]
  have hM0 : M ≠ 0 := hM.ne'
  have hs0 : s ≠ 0 := hs.ne'
  have hden : M ^ 2 + s ≠ 0 := by positivity
  have hpi : π ≠ 0 := pi_pos.ne'
  ext
  all_goals simp [nsmul_eq_mul]
  all_goals rw [← hs_def]
  all_goals field_simp
  all_goals ring
