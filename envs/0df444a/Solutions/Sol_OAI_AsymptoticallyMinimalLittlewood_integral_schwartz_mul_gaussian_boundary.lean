-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:06:06.369979+00:00
-- url     : https://prove2.me/submissions/2ee52864-4264-46c9-b45a-3e409e745b13

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Gaussian.lean:L63-L136
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

-- ---- from OAI.Analysis.Littlewood.Gaussian ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem integral_schwartz_mul_gaussian
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) (c : ℂ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
      2 * Real.pi * c * (x : ℂ))) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + Complex.I * c) ^ 2) := by
  have hG : Integrable (fun x : ℝ ↦
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) := by
    have hp : 0 < ((Real.pi : ℂ) * b).re := by
      simpa using mul_pos Real.pi_pos hb
    simpa only [neg_mul, add_zero] using
      integrable_cexp_quadratic hp (2 * Real.pi * c) 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner
    (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable hG
  have heq : (∫ x : ℝ, (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ))) x *
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) =
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        (𝓕 (fun x : ℝ ↦ Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
          2 * Real.pi * c * (x : ℂ)))) ξ := by
    simpa only [flip_innerₗ, smul_eq_mul] using! h
  rw [FourierTransform.fourier_fourierInv_eq] at heq
  rw [heq, fourier_gaussian_pi' hb c]
  simp_rw [← mul_assoc, mul_comm ((𝓕⁻ f : 𝓢(ℝ, ℂ)) _) (1 / b ^ (1 / 2 : ℂ)), mul_assoc]
  exact integral_const_mul _ _

/-- The damping kernel has modulus at most one on the closed right half-plane. -/
theorem norm_damped_quadratic_le_one {b : ℂ} (hb : 0 ≤ b.re) (u x : ℝ) :
    ‖Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x).re = -Real.pi * b.re * x ^ 2 := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hb) (sq_nonneg _)

/-- The Fourier-side Gaussian also has modulus at most one. -/
theorem norm_damped_fourier_le_one {b : ℂ} (hb : 0 ≤ b.re) (y : ℝ) :
    ‖Complex.exp (-Real.pi / b * (y : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi / b * (y : ℂ) ^ 2).re =
      -Real.pi * (b.re / Complex.normSq b) * y ^ 2 := by
    simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, pow_two,
      Complex.inv_re]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
      (div_nonneg hb (Complex.normSq_nonneg _))) (sq_nonneg _)

theorem integral_schwartz_mul_gaussian_boundary
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2) := by
  let bn : ℕ → ℂ := fun n ↦ b + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hbn (n : ℕ) : 0 < (bn n).re := by
    dsimp [bn]
    simpa using add_pos_of_nonneg_of_pos hb (by positivity : 0 < 1 / ((n : ℝ) + 1))
  have hbnlim : Filter.Tendsto bn Filter.atTop (𝓝 b) := by
    have hz := Complex.continuous_ofReal.tendsto 0 |>.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [bn] using tendsto_const_nhds.add hz
  have hblim : b ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases h : b.im = 0
    · left
      have hr : b.re ≠ 0 := by
        intro hr
        exact hb0 (Complex.ext hr h)
      exact lt_of_le_of_ne hb (Ne.symm hr)
    · exact Or.inr h
  have hcpow : Filter.Tendsto (fun n ↦ 1 / (bn n) ^ (1 / 2 : ℂ))
      Filter.atTop (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    exact tendsto_const_nhds.div
      (continuousAt_cpow_const hblim |>.tendsto.comp hbnlim)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hb0))
  have hl : Filter.Tendsto
      (fun n ↦ ∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) Filter.atTop
      (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact f.integrable.norm
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_damped_quadratic_le_one (hbn n).le u x)
    · filter_upwards with x
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          (((tendsto_const_nhds.mul hbnlim).mul tendsto_const_nhds).sub
            tendsto_const_nhds))
  have hr : Filter.Tendsto
      (fun n ↦ ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2)) Filter.atTop
      (𝓝 (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2))) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable.norm
    · intro n
      filter_upwards with ξ
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa only [Complex.ofReal_add] using norm_damped_fourier_le_one (hbn n).le (ξ + u)
    · filter_upwards with ξ
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          ((tendsto_const_nhds.div hbnlim hb0).mul tendsto_const_nhds))
  have heq (n : ℕ) :
      (∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) =
      1 / (bn n) ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2) := by
    convert integral_schwartz_mul_gaussian f (hbn n) (-Complex.I * u) using 1 <;>
      simp [← mul_assoc, sub_eq_add_neg]
  exact tendsto_nhds_unique hl ((hcpow.mul hr).congr' (Filter.Eventually.of_forall (fun n ↦ (heq n).symm)))

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary := @_root_.OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary
