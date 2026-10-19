-- Prove2me | solution 1 for MetricCodes.Spherical.zero_fibre_spectral_iff_classicalThreshold_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e76dff44-7c47-4792-9c8b-9e1afbc6c6d3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1) (ha : 0 < a) :
    s < 2 * MetricCodes.Gamma a 0 ↔ MetricCodes.classicalThreshold s < a := by
  have hvariance : 0 < a * (1 + a) := by positivity
  have hroot : 0 < Real.sqrt (a * (1 + a)) :=
    Real.sqrt_pos.mpr hvariance
  have hroot_sq := Real.sq_sqrt hvariance.le
  have hradical : 0 < 1 - s ^ 2 := by nlinarith
  have hclassical : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.mpr hradical
  have hclassical_sq := Real.sq_sqrt hradical.le
  have hlinear : 0 < 1 + 2 * a := by positivity
  rw [Gamma_zero ha]
  have hleft :
      s < 2 * (Real.sqrt (a * (1 + a)) / (1 + 2 * a)) ↔
        s * (1 + 2 * a) < 2 * Real.sqrt (a * (1 + a)) := by
    rw [← mul_div_assoc, lt_div_iff₀ hlinear]
  rw [hleft]
  have hsquares :
      (Real.sqrt (1 - s ^ 2) * (1 + 2 * a)) ^ 2 - 1 =
        (2 * Real.sqrt (a * (1 + a))) ^ 2 -
          (s * (1 + 2 * a)) ^ 2 := by
    rw [mul_pow, hclassical_sq, mul_pow, hroot_sq]
    ring
  have hcompare :
      s * (1 + 2 * a) < 2 * Real.sqrt (a * (1 + a)) ↔
        1 < Real.sqrt (1 - s ^ 2) * (1 + 2 * a) := by
    constructor
    · intro h
      have hsq := (sq_lt_sq₀
        (mul_nonneg hs.le hlinear.le)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hroot.le)).mpr h
      apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hclassical.le hlinear.le)).mp
      nlinarith [hsquares]
    · intro h
      have hsq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hclassical.le hlinear.le)).mpr h
      apply (sq_lt_sq₀
        (mul_nonneg hs.le hlinear.le)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hroot.le)).mp
      nlinarith [hsquares]
  rw [hcompare]
  unfold MetricCodes.classicalThreshold
  constructor
  · intro h
    have hdiv : 1 / Real.sqrt (1 - s ^ 2) < 1 + 2 * a := by
      apply (div_lt_iff₀ hclassical).mpr
      nlinarith
    linarith
  · intro h
    have hdiv : 1 / Real.sqrt (1 - s ^ 2) < 1 + 2 * a := by
      linarith
    have hmul := (div_lt_iff₀ hclassical).mp hdiv
    nlinarith
end MetricCodes.Spherical
