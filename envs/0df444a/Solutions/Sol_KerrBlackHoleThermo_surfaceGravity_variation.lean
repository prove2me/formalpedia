-- Prove2me | solution 1 for KerrBlackHoleThermo.surfaceGravity_variation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T11:08:42.9142+00:00
-- url     : https://prove2.me/submissions/ad9dc749-8b29-47b8-bf02-6eaabe467e95

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

set_option autoImplicit false

open Real

open KerrBlackHoleThermo in
theorem kerrSGV_rPlus_sq_add (M a : ℝ) (ha : a ^ 2 ≤ M ^ 2) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * (M + √(M ^ 2 - a ^ 2)) := by
  have hs2 : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  unfold rPlus
  linear_combination hs2

open KerrBlackHoleThermo in
theorem kerrSGV_horizonArea_eq (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
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
    cos_pi, cos_zero, kerrSGV_rPlus_sq_add M a ha]
  ring

open KerrBlackHoleThermo in
theorem kerrSGV_area_eq_on (p : ℝ × ℝ) (h1 : 0 < p.1) (h2 : p.2 ^ 2 < p.1 ^ 4) :
    horizonArea p.1 (p.2 / p.1) = 8 * π * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2)) := by
  have hle : (p.2 / p.1) ^ 2 ≤ p.1 ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith
  rw [kerrSGV_horizonArea_eq _ _ h1 hle]
  have hfac : p.1 ^ 4 - p.2 ^ 2 = p.1 ^ 2 * (p.1 ^ 2 - (p.2 / p.1) ^ 2) := by
    field_simp
  rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1.le]
  ring

open KerrBlackHoleThermo in
theorem kerrSGV_root_eq (p : ℝ × ℝ) (h1 : 0 < p.1) (_h2 : p.2 ^ 2 < p.1 ^ 4) :
    √(p.1 ^ 2 - (p.2 / p.1) ^ 2) = √(p.1 ^ 4 - p.2 ^ 2) / p.1 := by
  have hfac : p.1 ^ 4 - p.2 ^ 2 = p.1 ^ 2 * (p.1 ^ 2 - (p.2 / p.1) ^ 2) := by
    field_simp
  rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1.le]
  field_simp

open KerrBlackHoleThermo in
theorem kerrSGV_kappa_on (p : ℝ × ℝ) (h1 : 0 < p.1) (h2 : p.2 ^ 2 < p.1 ^ 4) :
    surfaceGravity p.1 (p.2 / p.1)
      = √(p.1 ^ 4 - p.2 ^ 2) / (2 * p.1 * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2))) := by
  unfold surfaceGravity
  rw [kerrSGV_root_eq p h1 h2]
  have h0 : 0 ≤ √(p.1 ^ 4 - p.2 ^ 2) := Real.sqrt_nonneg _
  have hp : p.1 ≠ 0 := h1.ne'
  have hd : p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2) ≠ 0 := by positivity
  field_simp

open KerrBlackHoleThermo in
theorem kerrSGV_omega_on (p : ℝ × ℝ) (h1 : 0 < p.1) (h2 : p.2 ^ 2 < p.1 ^ 4) :
    horizonAngularVelocity p.1 (p.2 / p.1)
      = p.2 / (2 * p.1 * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2))) := by
  unfold horizonAngularVelocity
  rw [kerrSGV_root_eq p h1 h2]
  have h0 : 0 ≤ √(p.1 ^ 4 - p.2 ^ 2) := Real.sqrt_nonneg _
  have hp : p.1 ≠ 0 := h1.ne'
  have hd : p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2) ≠ 0 := by positivity
  field_simp

open KerrBlackHoleThermo Real in
theorem solution (M J : ℝ) (hM : 0 < M) (hJ : J ^ 2 < M ^ 4) :
    ∃ dκ dΩ : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => surfaceGravity p.1 (p.2 / p.1)) dκ (M, J) ∧
      HasFDerivAt (fun p : ℝ × ℝ => horizonAngularVelocity p.1 (p.2 / p.1)) dΩ (M, J) ∧
      ContinuousLinearMap.fst ℝ ℝ ℝ
        = (-(horizonArea M (J / M) / (4 * π))) • dκ - (2 * J) • dΩ := by
  have hspos : 0 < M ^ 4 - J ^ 2 := by linarith
  set s := √(M ^ 4 - J ^ 2) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hspos
  have hs2 : s ^ 2 = M ^ 4 - J ^ 2 := Real.sq_sqrt hspos.le
  have hfst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (M, J) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (M, J) := hasFDerivAt_snd
  have hq : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ 4 - p.2 ^ 2)
      ((4 * M ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ - (2 * J) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (M, J) := by
    have := (hfst.pow 4).sub (hsnd.pow 2)
    refine this.congr_fderiv ?_
    ext <;> (simp [nsmul_eq_mul]; try ring)
  have hsq := hq.sqrt (by simp; exact hspos.ne')
  have hD := (((hfst.pow 2).add hsq).const_mul 2).mul hfst
  have hD' := hD.congr_of_eventuallyEq
    (f₁ := fun p : ℝ × ℝ => 2 * p.1 * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2)))
    (Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply, Pi.add_apply]; ring)
  have hDne : (2 * (M, J).1 * ((M, J).1 ^ 2 + √((M, J).1 ^ 4 - (M, J).2 ^ 2))) ≠ 0 := by
    simp only; rw [← hs_def]; positivity
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) hDne).comp (M, J) hD'
  have hk := hsq.mul hinv
  have ho := hsnd.mul hinv
  have hopen : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ^ 2 < p.1 ^ 4} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_snd.pow 2) (continuous_fst.pow 4))
  have hek : (fun p : ℝ × ℝ => surfaceGravity p.1 (p.2 / p.1)) =ᶠ[nhds (M, J)]
      (fun p : ℝ × ℝ => √(p.1 ^ 4 - p.2 ^ 2) * ((fun x : ℝ => x⁻¹) ∘ (fun p : ℝ × ℝ => 2 * p.1 * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2)))) p) := by
    filter_upwards [hopen.mem_nhds ⟨hM, hJ⟩] with p hp
    simp only [Function.comp_apply]
    rw [kerrSGV_kappa_on p hp.1 hp.2, div_eq_mul_inv]
  have heo : (fun p : ℝ × ℝ => horizonAngularVelocity p.1 (p.2 / p.1)) =ᶠ[nhds (M, J)]
      (fun p : ℝ × ℝ => p.2 * ((fun x : ℝ => x⁻¹) ∘ (fun p : ℝ × ℝ => 2 * p.1 * (p.1 ^ 2 + √(p.1 ^ 4 - p.2 ^ 2)))) p) := by
    filter_upwards [hopen.mem_nhds ⟨hM, hJ⟩] with p hp
    simp only [Function.comp_apply]
    rw [kerrSGV_omega_on p hp.1 hp.2, div_eq_mul_inv]
  refine ⟨_, _, hk.congr_of_eventuallyEq hek, ho.congr_of_eventuallyEq heo, ?_⟩
  have hA : horizonArea M (J / M) = 8 * π * (M ^ 2 + s) := kerrSGV_area_eq_on (M, J) hM hJ
  rw [hA]
  have hM0 : M ≠ 0 := hM.ne'
  have hs0 : s ≠ 0 := hs.ne'
  have hden : M ^ 2 + s ≠ 0 := by positivity
  have hpi : π ≠ 0 := pi_pos.ne'
  ext
  all_goals simp [nsmul_eq_mul]
  all_goals rw [← hs_def]
  all_goals field_simp
  all_goals ring_nf
  · linear_combination (-48 * M ^ 2 * s - 32 * M ^ 4 - 16 * s ^ 2) * hs2
  · linear_combination (8 * J) * hs2
