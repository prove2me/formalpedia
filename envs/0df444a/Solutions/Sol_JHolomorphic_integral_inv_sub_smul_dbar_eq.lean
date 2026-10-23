-- Prove2me | solution 1 for JHolomorphic.integral_inv_sub_smul_dbar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:50:30.091826+00:00
-- url     : https://prove2.me/submissions/3084e3ed-c8dd-4b4b-b0f7-5e91d116e18c

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set

theorem integral_inv_sub_smul_dbar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (z : ℂ)
    (hint : Integrable (fun ζ => (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I))) :
    ∫ ζ, (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I) =
      (2 * Real.pi : ℂ) • h z := by
  rw [NormedSpace.eq_iff_forall_dual_eq ℂ]
  intro ℓ
  have hℓh : ContDiff ℝ 1 (fun x => ℓ (h x)) := (ℓ.restrictScalars ℝ).contDiff.comp hh
  have hℓc : HasCompactSupport (fun x => ℓ (h x)) := hc.comp_left (map_zero ℓ)
  have hder : ∀ ζ v, fderiv ℝ (fun x => ℓ (h x)) ζ v = ℓ (fderiv ℝ h ζ v) := by
    intro ζ v
    have hd : HasFDerivAt (fun x => ℓ (h x)) ((ℓ.restrictScalars ℝ).comp (fderiv ℝ h ζ)) ζ :=
      (ℓ.restrictScalars ℝ).hasFDerivAt.comp ζ ((hh.differentiable one_ne_zero) ζ).hasFDerivAt
    rw [hd.fderiv]
    rfl
  have hP := Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul z _ hℓh hℓc
  simp_rw [hder] at hP
  rw [← ContinuousLinearMap.integral_comp_comm ℓ hint, map_smul, smul_eq_mul]
  have hrw : ∀ ζ, ℓ ((z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I)) =
      (-2 : ℂ) * ((ζ - z)⁻¹ * ((ℓ (fderiv ℝ h ζ 1) + Complex.I * ℓ (fderiv ℝ h ζ Complex.I)) / 2)) := by
    intro ζ
    rw [map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]
    rcases eq_or_ne ζ z with rfl | hne
    · simp
    · have : z - ζ = -(ζ - z) := by ring
      rw [this, inv_neg]
      ring
  simp_rw [hrw]
  rw [integral_const_mul, hP]
  ring

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Convolution

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (z : ℂ)
    (hint : Integrable (fun ζ => (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I))) :
    ∫ ζ, (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I) =
      (2 * Real.pi : ℂ) • h z :=
  integral_inv_sub_smul_dbar h hh hc z hint
