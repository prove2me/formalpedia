-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:11:14.68026+00:00
-- url     : https://prove2.me/submissions/2f81ac70-103e-4db7-8753-69a4321e56b6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Gaussian.lean:L208-L269
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_integral_schwartz_quadratic_exact

-- ---- from OAI.Analysis.Littlewood.Gaussian ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Multiplication by a continuous real phase preserves integrability. -/
theorem integrable_schwartz_phase (f : 𝓢(ℝ, ℂ)) (p : ℝ → ℝ)
    (hp : Continuous p) : Integrable (fun x ↦ f x * realPhase (p x)) := by
  apply f.integrable.norm.mono'
  · apply Continuous.aestronglyMeasurable
    unfold realPhase
    exact f.continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hp)))
  · filter_upwards with x
    simp

/-- Fourier inversion specialized to the linear factor in the quadratic formula. -/
theorem integral_schwartz_inverse_linear (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-2 * Real.pi * ξ * x)) = f x := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g x)
    (show (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from
      FourierTransform.fourier_fourierInv_eq f)
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul, realPhase, mul_comm]

/-- The remaining quadratic Fourier multiplier differs from one by at most
π ξ² / |t|, uniformly in the stationary point. -/
theorem norm_quadratic_multiplier_sub_one {t : ℝ} (ξ : ℝ) :
    ‖realPhase (-Real.pi / t * ξ ^ 2) - 1‖ ≤ Real.pi / |t| * ξ ^ 2 := by
  calc
    _ ≤ ‖-Real.pi / t * ξ ^ 2‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_nonneg (sq_nonneg ξ)]

theorem uniform_quadratic_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ Real.pi / |t| * (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) ∧
      (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
        (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
          realPhase (-Real.pi / t * u ^ 2)) * (f (u / t) + E) := by
  let p : ℝ → ℝ := fun ξ ↦ -2 * Real.pi * ξ * (u / t)
  let q : ℝ → ℝ := fun ξ ↦ -Real.pi / t * ξ ^ 2
  let d : ℝ → ℂ := fun ξ ↦ (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ) * (realPhase (q ξ) - 1)
  have hp : Continuous p := by unfold p; fun_prop
  have hq : Continuous q := by unfold q; fun_prop
  have hl := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) p hp
  have ht' := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) (fun ξ ↦ p ξ + q ξ) (hp.add hq)
  have hd : Integrable d := by
    convert ht'.sub hl using 1
    ext ξ
    simp only [d, realPhase_add, Pi.sub_apply]
    ring
  refine ⟨∫ ξ, d ξ, ?_, ?_⟩
  · have hm : Integrable (fun ξ : ℝ ↦ ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
      have h : Integrable (fun ξ : ℝ ↦ ‖ξ‖ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) :=
        (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable_pow_mul volume 2
      simpa only [Real.norm_eq_abs, sq_abs] using h
    calc
      ‖∫ ξ, d ξ‖ ≤ ∫ ξ, ‖d ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ, (Real.pi / |t|) * (ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
        apply integral_mono hd.norm (hm.const_mul _)
        intro ξ
        simp only [d, norm_mul, norm_realPhase, mul_one]
        calc
          _ ≤ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖ * (Real.pi / |t| * ξ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_quadratic_multiplier_sub_one ξ) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  · have hlin : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ)) = f (u / t) :=
      integral_schwartz_inverse_linear f (u / t)
    have hsum : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) =
        f (u / t) + ∫ ξ, d ξ := by
      rw [← hlin, ← integral_add hl hd]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [d, realPhase_add]
      ring
    have hphase (ξ : ℝ) :
        realPhase (-Real.pi / t * (ξ + u) ^ 2) =
          realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ) := by
      rw [← realPhase_add]
      congr 1
      dsimp [p, q]
      ring
    rw [integral_schwartz_quadratic_exact f ht u]
    simp_rw [hphase]
    have hi : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
          (realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ))) =
        realPhase (-Real.pi / t * u ^ 2) *
          (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      ring
    rw [hi, hsum]
    ring

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error := @_root_.OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error
