-- Prove2me | solution 1 for MetricCodes.Spherical.eventually_Gamma_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/1cd6f493-541e-4916-8892-c5a6e9ac5129

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Gamma_eq_sub
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_sphericalImprovementSlope_gt_one
import Theorems.Thm_MetricCodes_Spherical_sphericalSpectralMarginPolynomial_factor
import Theorems.Thm_MetricCodes_Spherical_sphericalSpectralMarginPolynomial_continuous
import Theorems.Thm_MetricCodes_Spherical_sphericalSpectralMarginPolynomial_improvement_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.Gamma a 0 <
        MetricCodes.Gamma (sphericalImprovementPath a b) b := by
  have hzero :
      0 < sphericalSpectralMarginPolynomial a
        (sphericalImprovementSlope a) 0 := by
    rw [sphericalSpectralMarginPolynomial_improvement_zero]
    positivity
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < sphericalSpectralMarginPolynomial a
          (sphericalImprovementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (sphericalSpectralMarginPolynomial a
            (sphericalImprovementSlope a)) 0 :=
      (sphericalSpectralMarginPolynomial_continuous
        a (sphericalImprovementSlope a)).continuousAt
    exact nhdsWithin_le_nhds
      (hcontinuous.tendsto.eventually (lt_mem_nhds hzero))
  have hc : 1 < sphericalImprovementSlope a :=
    sphericalImprovementSlope_gt_one ha
  filter_upwards [hpoly, self_mem_nhdsWithin]
    with b hbpoly (hb : 0 < b)
  have hbpath : b < sphericalImprovementPath a b := by
    unfold sphericalImprovementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < sphericalImprovementPath a b :=
    hb.trans hbpath
  have hbase : 0 < a * (1 + a) := by positivity
  have hrad :
      0 < sphericalImprovementPath a b *
        (1 + sphericalImprovementPath a b) := by positivity
  have hnum :
      0 < sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b) := by
    have hfactor :
        0 < (sphericalImprovementPath a b - b) *
          (1 + sphericalImprovementPath a b + b) := by positivity
    nlinarith
  have hmargin :
      0 <
        ((sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
          (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    have hfactor := sphericalSpectralMarginPolynomial_factor
      a (sphericalImprovementSlope a) b
    change
      0 < (((a + sphericalImprovementSlope a * b) *
          (1 + (a + sphericalImprovementSlope a * b)) -
            b * (1 + b)) * (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * (a + sphericalImprovementSlope a * b)) ^ 2 *
            ((a + sphericalImprovementSlope a * b) *
              (1 + (a + sphericalImprovementSlope a * b)))
    rw [hfactor]
    exact mul_pos hb hbpoly
  have hleftnonneg :
      0 ≤ Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) := by
    positivity
  have hrightpos :
      0 < (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
        (1 + 2 * a) := by positivity
  have hsquare :
      (Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)))) ^ 2 =
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase.le,
      Real.sq_sqrt hrad.le]
    ring
  have hcross :
      Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) <
        (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
            (1 + 2 * a) := by
    nlinarith
  rw [Gamma_zero ha, MetricCodes.Gamma_eq_sub]
  have hlin : 0 < 1 + 2 * a := by positivity
  have hden :
      0 < (1 + 2 * sphericalImprovementPath a b) *
        Real.sqrt
          (sphericalImprovementPath a b *
            (1 + sphericalImprovementPath a b)) := by positivity
  exact (div_lt_div_iff₀ hlin hden).2 hcross
end MetricCodes.Spherical
