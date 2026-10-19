-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_beta_half_half_eq_integral_measureT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/77caf484-9212-4134-b409-094b441ae6ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_betaPDFReal_half_half_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology
open MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
namespace MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
theorem _root_.solution (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) =
      (1 / Real.pi) *
        ∫ z, f ((z + 1) / 2) ∂Polynomial.Chebyshev.measureT := by
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hfinite : ∀ᵐ u : ℝ ∂volume,
      betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) u < ⊤ := by
    filter_upwards [] with u
    simp [betaPDF]
  have hpdf (u : ℝ) :
      0 ≤ betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u := by
    by_cases hu : 0 < u ∧ u < 1
    · exact (betaPDFReal_pos hu.1 hu.2 (by norm_num) (by norm_num)).le
    · simp [betaPDFReal, hu]
  unfold betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  simp_rw [betaPDF, ENNReal.toReal_ofReal (hpdf _), smul_eq_mul]
  rw [Polynomial.Chebyshev.integral_measureT,
    ← intervalIntegral.integral_const_mul]
  have hsupport :
      (∫ u : ℝ, betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u) =
        ∫ u in (0 : ℝ)..1,
          betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) 1
    · simp [hu]
    · have hu' : ¬ (0 < u ∧ u < 1) := by simpa using hu
      simp [hu, betaPDFReal, hu']
  rw [hsupport]
  let g : ℝ → ℝ := fun z =>
    (1 / Real.pi) * (f ((z + 1) / 2) * (Real.sqrt (1 - z ^ 2))⁻¹)
  have hchange :
      (∫ u in (0 : ℝ)..1, g (2 * u - 1) * 2) =
        ∫ z in (-1 : ℝ)..1, g z := by
    convert intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 2 * u - 1) (f' := fun _ : ℝ => 2)
      (g := g)
      (by fun_prop)
      (fun u _ => by
        simpa using
          (((hasDerivAt_const (x := u) (c := (2 : ℝ))).mul
            (hasDerivAt_id u)).sub_const 1))
      (fun _ _ => by norm_num) using 1 <;> norm_num
  dsimp [g] at hchange
  simp_rw [Real.sqrt_inv]
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro u hu
  change betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u =
    (1 / Real.pi) *
      (f ((2 * u - 1 + 1) / 2) *
        (Real.sqrt (1 - (2 * u - 1) ^ 2))⁻¹) * 2
  have hu₀ : 0 ≤ u := by simpa using hu.1
  have hu₁ : u ≤ 1 := by simpa using hu.2
  by_cases hzero : u = 0 ∨ u = 1
  · rcases hzero with rfl | rfl <;> norm_num [betaPDFReal]
  · have hzero₀ : u ≠ 0 := fun h => hzero (Or.inl h)
    have hzero₁ : u ≠ 1 := fun h => hzero (Or.inr h)
    have hupos : 0 < u := lt_of_le_of_ne hu₀ (Ne.symm hzero₀)
    have huone : u < 1 := lt_of_le_of_ne hu₁ hzero₁
    rw [betaPDFReal_half_half_eq u hupos huone]
    have hquad : 1 - (2 * u - 1) ^ 2 = 4 * (u * (1 - u)) := by ring
    have hsqrt :
        Real.sqrt (1 - (2 * u - 1) ^ 2) =
          2 * Real.sqrt (u * (1 - u)) := by
      rw [hquad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hsqrt]
    have harg : (2 * u - 1 + 1) / 2 = u := by ring
    rw [harg]
    field_simp
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
