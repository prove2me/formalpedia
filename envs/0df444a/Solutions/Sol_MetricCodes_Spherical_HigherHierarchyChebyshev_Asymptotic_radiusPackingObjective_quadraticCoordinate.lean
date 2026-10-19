-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusPackingObjective_quadraticCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/3d8f725f-3946-4a50-9a8a-bde595d6471d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_one_sub_two_mul_radiusGamma
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_inverseQuadratic_quadraticCoordinate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusNormalizer_quadraticCoordinate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_log_two_mul_sphericalEntropy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    radiusPackingObjective (a * (1 + a)) = degreePackingObjective a := by
  have ha' : 0 ≤ a := ha.le
  have hden : 0 < 1 + 2 * a := by linarith
  have hx : 0 < 1 / (1 + 2 * a) := by positivity
  have harcsin : 0 < Real.arcsin (1 / (1 + 2 * a)) :=
    Real.arcsin_pos.mpr hx
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hxne : 1 / (1 + 2 * a) ≠ 0 := hx.ne'
  have hlogratio :
      Real.log (1 + 2 * a) - Real.log (1 + a) =
        Real.log ((1 + 2 * a) / (1 + a)) := by
    rw [Real.log_div (by linarith : 1 + 2 * a ≠ 0)
      (by linarith : 1 + a ≠ 0)]
  have harcsin_factor :
      Real.arcsin (1 / (1 + 2 * a)) =
        (1 / (1 + 2 * a)) *
          (Real.arcsin (1 / (1 + 2 * a)) / (1 / (1 + 2 * a))) := by
    field_simp
  have hratio_pos :
      0 < Real.arcsin (1 / (1 + 2 * a)) / (1 / (1 + 2 * a)) :=
    div_pos harcsin hx
  have hlogarcsin :
      Real.log (Real.arcsin (1 / (1 + 2 * a))) =
        -Real.log (1 + 2 * a) +
          Real.log (Real.arcsin (1 / (1 + 2 * a)) /
            (1 / (1 + 2 * a))) := by
    nth_rewrite 1 [harcsin_factor]
    rw [Real.log_mul hxne hratio_pos.ne']
    simp [one_div, Real.log_inv]
  unfold radiusPackingObjective
    MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective
  rw [one_sub_two_mul_radiusGamma,
    radiusNormalizer_quadraticCoordinate ha',
    radiusEntropy, inverseQuadratic_quadraticCoordinate ha']
  have hdivision :
      2 / ((2 / Real.pi) * Real.arcsin (1 / (1 + 2 * a))) =
        Real.pi / Real.arcsin (1 / (1 + 2 * a)) := by
    field_simp
  rw [hdivision, Real.logb,
    Real.log_div hpi harcsin.ne', hlogarcsin]
  unfold degreePackingObjective
  rw [← hlogratio]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hentropy :
      MetricCodes.sphericalEntropy a =
        (Real.log (1 + a) + a * Real.log (1 + 1 / a)) / Real.log 2 := by
    apply (eq_div_iff hlog).mpr
    nlinarith [log_two_mul_sphericalEntropy ha]
  rw [hentropy]
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
