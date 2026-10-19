-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_openingRegularGamma_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/602cdb56-3a02-491e-8a42-328938db5197

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingRegularGamma_scaledDerivative
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingRegularGamma_zero

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) (η : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (openingRegularGamma a b η t - Gamma a b) / t)
      (𝓝[>] 0)
      (nhds (η * deriv (openingRegularGamma a b 1) 0)) := by
  obtain ⟨_, d, hd, hunit⟩ :=
    openingRegularGamma_scaledDerivative h hzero η
  have hdvalue : d = deriv (openingRegularGamma a b 1) 0 :=
    hunit.deriv.symm
  have hslope := hd.tendsto_slope_zero_right
  rw [hdvalue] at hslope
  simpa [openingRegularGamma_zero hzero, div_eq_mul_inv,
    smul_eq_mul, mul_comm] using hslope
end MetricCodes.Spherical.HigherHierarchy
