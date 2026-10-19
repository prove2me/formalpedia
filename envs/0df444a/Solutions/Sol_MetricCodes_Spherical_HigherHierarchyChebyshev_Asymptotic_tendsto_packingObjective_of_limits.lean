-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_packingObjective_of_limits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/2a05e618-b181-44ff-84ff-7dd23e921825

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusNormalizer_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_one_sub_two_mul_radiusGamma

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchyChebyshev
open MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
noncomputable section
open Filter
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    {R : ℝ} (hR : 0 ≤ R) {G P : ℕ → ℝ}
    (hG : Tendsto G atTop (𝓝 (radiusGamma R)))
    (hP : Tendsto P atTop (𝓝 (radiusEntropy R))) :
    Tendsto
      (fun n => MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective
        (G n) (P n))
      atTop (𝓝 (radiusPackingObjective R)) := by
  have hnormalizer : 0 < 1 - 2 * radiusGamma R := by
    rw [one_sub_two_mul_radiusGamma]
    exact radiusNormalizer_pos hR
  have hdenominator :
      Tendsto (fun n => 1 - 2 * G n) atTop
        (𝓝 (1 - 2 * radiusGamma R)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hG)
  have hquotient :
      Tendsto (fun n => 2 / (1 - 2 * G n)) atTop
        (𝓝 (2 / (1 - 2 * radiusGamma R))) :=
    tendsto_const_nhds.div hdenominator hnormalizer.ne'
  have hquotient_ne : (2 : ℝ) / (1 - 2 * radiusGamma R) ≠ 0 :=
    div_ne_zero (by norm_num) hnormalizer.ne'
  have hlogarithm :
      Tendsto (fun n => Real.logb 2 (2 / (1 - 2 * G n))) atTop
        (𝓝 (Real.logb 2 (2 / (1 - 2 * radiusGamma R)))) :=
    (Real.continuousAt_logb hquotient_ne).tendsto.comp hquotient
  exact (tendsto_const_nhds.mul hlogarithm).sub hP
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
