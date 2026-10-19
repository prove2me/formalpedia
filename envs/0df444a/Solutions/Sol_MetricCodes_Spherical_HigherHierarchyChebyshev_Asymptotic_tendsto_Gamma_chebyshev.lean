-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_Gamma_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/e68d380b-b473-4df5-a00b-546939f7ee34

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_midpointAverage_integral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAtom_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_Gamma_eq_midpointAverage
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_integral_angularAtom_eq_radiusGamma

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open Filter
open scoped Topology BigOperators
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Gamma
        (ambient R r) (stabilizer R r))
      atTop (𝓝 (radiusGamma R)) := by
  have hmid := (tendsto_midpointAverage_integral
    (angularAtom_antitone hR)).comp (tendsto_add_atTop_nat 1)
  rw [integral_angularAtom_eq_radiusGamma hR] at hmid
  apply hmid.congr'
  exact Filter.Eventually.of_forall (fun r =>
    (Gamma_eq_midpointAverage hR r).symm)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
