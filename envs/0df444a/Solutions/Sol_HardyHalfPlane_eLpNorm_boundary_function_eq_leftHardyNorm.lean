-- Prove2me | solution 1 for HardyHalfPlane.eLpNorm_boundary_function_eq_leftHardyNorm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:27:09.947742+00:00
-- url     : https://prove2.me/submissions/8193dba8-a33d-4ae6-838b-ef77965ae10f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy
import Theorems.Thm_HardyHalfPlane_cauchy_integral_formula

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_eLpNorm_boundary_function_eq_leftHardyNorm

open ProbabilityTheory

/-- The Poisson kernel of the half-plane as the difference of two Cauchy kernels. -/
lemma kernel_identity (a σ t y : ℝ) (hσ : σ < a) :
    (1 / (2 * (Real.pi : ℂ))) *
      (1 / ((a : ℂ) + (y : ℂ) * Complex.I - ((σ : ℂ) + (t : ℂ) * Complex.I)) -
        1 / ((a : ℂ) + (y : ℂ) * Complex.I - (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
      ((Real.pi⁻¹ * (a - σ) * ((y - t) ^ 2 + (a - σ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hδ : 0 < a - σ := sub_pos.2 hσ
  set δ := a - σ with hδdef
  set u := y - t with hu
  have e1 : (a : ℂ) + (y : ℂ) * Complex.I - ((σ : ℂ) + (t : ℂ) * Complex.I) =
      (δ : ℂ) + (u : ℂ) * Complex.I := by
    rw [hδdef, hu]; push_cast; ring
  have e2 : (a : ℂ) + (y : ℂ) * Complex.I - (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      -(δ : ℂ) + (u : ℂ) * Complex.I := by
    rw [hδdef, hu]; push_cast; ring
  rw [e1, e2]
  have n1 : (δ : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have n2 : -(δ : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have n3r : u ^ 2 + δ ^ 2 ≠ 0 := by positivity
  have n3 : (u : ℂ) ^ 2 + (δ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast n3r
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : ((δ : ℂ) + (u : ℂ) * Complex.I) * (-(δ : ℂ) + (u : ℂ) * Complex.I) =
      -((u : ℂ) ^ 2 + (δ : ℂ) ^ 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [div_sub_div _ _ n1 n2, hprod]
  push_cast
  field_simp
  ring

/-- The Cauchy density is symmetric in its location and its variable. -/
lemma cauchyPDF_symm (t y : ℝ) (γ : NNReal) : cauchyPDF t γ y = cauchyPDF y γ t := by
  simp only [cauchyPDF, cauchyPDFReal]
  congr 2
  ring

/-- Each line function of `Φ` has `L^p` norm at most that of the boundary function: the Poisson
representation coming from the Cauchy formula, Jensen's inequality for the Cauchy (Poisson)
probability measure, and Tonelli. -/
lemma line_eLpNorm_le (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : HardyHalfPlane.MemLeftHardy Φ a p) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y)))
    (hg_meas : AEStronglyMeasurable g volume) (σ : ℝ) (hσ : σ < a) :
    eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume ≤ eLpNorm g p volume := by
  set δ : NNReal := ⟨a - σ, (sub_pos.2 hσ).le⟩ with hδ
  have hδc : (δ : ℝ) = a - σ := rfl
  have hδ0 : δ ≠ 0 := by
    intro h
    have : (δ : ℝ) = 0 := by rw [h]; rfl
    rw [hδc] at this; linarith
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- pointwise bound by the Poisson integral of `‖g‖`
  have hpt : ∀ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ₑ ≤
      ∫⁻ y, cauchyPDF t δ y * ‖g y‖ₑ := by
    intro t
    have hz1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re ≠ a := by simp; linarith
    have hz2 : (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re ≠ a := by simp; linarith
    obtain ⟨hi1, he1⟩ := HardyHalfPlane.cauchy_integral_formula Φ a p hp1 hp hΦ a le_rfl g hg _ hz1
    obtain ⟨hi2, he2⟩ := HardyHalfPlane.cauchy_integral_formula Φ a p hp1 hp hΦ a le_rfl g hg _ hz2
    have hre1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re < a := by simp; linarith
    have hre2 : ¬ (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re < a := by simp; linarith
    rw [if_pos hre1] at he1
    rw [if_neg hre2] at he2
    have key : Φ ((σ : ℂ) + (t : ℂ) * Complex.I) =
        ∫ y : ℝ, (1 / (2 * (Real.pi : ℂ))) *
          (g y / ((a : ℂ) + (y : ℂ) * Complex.I - ((σ : ℂ) + (t : ℂ) * Complex.I)) -
            g y / ((a : ℂ) + (y : ℂ) * Complex.I -
              (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
      rw [integral_const_mul, integral_sub hi1 hi2, mul_sub, he1, he2, sub_zero]
    rw [key]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    have hk := kernel_identity a σ t y hσ
    have hpos : 0 ≤ Real.pi⁻¹ * (a - σ) * ((y - t) ^ 2 + (a - σ) ^ 2)⁻¹ := by
      have : 0 < a - σ := sub_pos.2 hσ
      positivity
    have : (1 / (2 * (Real.pi : ℂ))) *
          (g y / ((a : ℂ) + (y : ℂ) * Complex.I - ((σ : ℂ) + (t : ℂ) * Complex.I)) -
            g y / ((a : ℂ) + (y : ℂ) * Complex.I -
              (((2 * a - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
        ((Real.pi⁻¹ * (a - σ) * ((y - t) ^ 2 + (a - σ) ^ 2)⁻¹ : ℝ) : ℂ) * g y := by
      rw [← hk]; ring
    rw [this, enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hpos]
    rfl
  -- Jensen's inequality for the probability measure `cauchyMeasure t δ`
  have hjensen : ∀ t : ℝ, (∫⁻ y, cauchyPDF t δ y * ‖g y‖ₑ) ^ p.toReal ≤
      ∫⁻ y, cauchyPDF t δ y * ‖g y‖ₑ ^ p.toReal := by
    intro t
    have hν := cauchyMeasure_of_scale_ne_zero t hδ0
    have hgν : AEStronglyMeasurable g (cauchyMeasure t δ) := by
      rw [hν]; exact hg_meas.mono_ac (withDensity_absolutelyContinuous _ _)
    have h := eLpNorm_le_eLpNorm_of_exponent_le hp1 hgν
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, hν,
      lintegral_withDensity_eq_lintegral_mul₀ (measurable_cauchyPDF t δ).aemeasurable
        hg_meas.aemeasurable.enorm,
      lintegral_withDensity_eq_lintegral_mul₀ (measurable_cauchyPDF t δ).aemeasurable
        (hg_meas.aemeasurable.enorm.pow_const _)] at h
    rw [one_div, ENNReal.le_rpow_inv_iff hr] at h
    exact h
  -- integrate in `t` and swap the order of integration
  have hmeasK : Measurable (fun q : ℝ × ℝ => cauchyPDF q.1 δ q.2) := by
    simp only [cauchyPDF, cauchyPDFReal]
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hswap : AEMeasurable (Function.uncurry fun t y => cauchyPDF t δ y * ‖g y‖ₑ ^ p.toReal)
      (volume.prod volume) :=
    hmeasK.aemeasurable.mul (hg_meas.aemeasurable.enorm.pow_const _).comp_snd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∫⁻ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ₑ ^ p.toReal
      ≤ ∫⁻ t : ℝ, ∫⁻ y : ℝ, cauchyPDF t δ y * ‖g y‖ₑ ^ p.toReal :=
        lintegral_mono fun t => (ENNReal.rpow_le_rpow (hpt t) hr.le).trans (hjensen t)
    _ = ∫⁻ y : ℝ, ∫⁻ t : ℝ, cauchyPDF t δ y * ‖g y‖ₑ ^ p.toReal := lintegral_lintegral_swap hswap
    _ = ∫⁻ y : ℝ, ‖g y‖ₑ ^ p.toReal := by
        refine lintegral_congr fun y => ?_
        simp_rw [cauchyPDF_symm _ y δ]
        rw [lintegral_mul_const _ (measurable_cauchyPDF y δ), lintegral_cauchyPDF_eq_one y hδ0,
          one_mul]

end Sol_HardyHalfPlane_eLpNorm_boundary_function_eq_leftHardyNorm

open HardyHalfPlane in
theorem solution (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hΦ : MemLeftHardy Φ a p) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y))) :
    eLpNorm g p volume = leftHardyNorm Φ a p := by
  -- the line functions are continuous
  have hcont : ∀ σ : ℝ, σ < a →
      Continuous (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
    intro σ hσ
    refine hΦ.1.continuousOn.comp_continuous (by fun_prop) ?_
    intro y
    simp [hσ]
  -- a sequence `s n ↑ a`
  set s : ℕ → ℝ := fun n => a - 1 / ((n : ℝ) + 1) with hs
  have hs_lt : ∀ n, s n < a := fun n => by
    simp only [hs]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hs_tend : Tendsto s atTop (𝓝[<] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs_lt⟩
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub a
    simpa [hs] using h
  have h_lim : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun n => Φ ((s n : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 (g y)) :=
    hg.mono fun y hy => hy.comp hs_tend
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun y : ℝ => Φ ((s n : ℂ) + (y : ℂ) * Complex.I)) volume :=
    fun n => (hcont _ (hs_lt n)).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas h_lim
  apply le_antisymm
  · -- Fatou's lemma along the lines `Re s = s n`
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas g h_lim).trans ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ < a) =>
      eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume) (s n) (hs_lt n) le_rfl
  · -- the Poisson representation bounds every line norm by the boundary norm
    refine iSup₂_le fun σ hσ => ?_
    exact Sol_HardyHalfPlane_eLpNorm_boundary_function_eq_leftHardyNorm.line_eLpNorm_le
      Φ a p hp1 hp hΦ g hg hg_meas σ hσ
