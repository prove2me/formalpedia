-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_opening_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/a97814b1-550c-4e5d-a67e-f9e860def27c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_spectralAtom_sq_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_opening_eq_regular_add
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_opening_terminalWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_openingRegularGamma_slope

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
        (Gamma (openingAmbient a (η * t) (t ^ 2)) b - Gamma a b) / t)
      (𝓝[>] 0)
      (nhds (η * deriv (openingRegularGamma a b 1) 0 +
        lagrangeWeight a b (Fin.last r))) := by
  have hregular := tendsto_openingRegularGamma_slope h hzero η
  have hterminal :=
    (tendsto_opening_terminalWeight h hzero η).mul
      tendsto_spectralAtom_sq_div
  have hsum := hregular.add hterminal
  have heq :
      (fun t : ℝ =>
        (Gamma (openingAmbient a (η * t) (t ^ 2)) b - Gamma a b) / t)
        =ᶠ[𝓝[>] 0]
      (fun t =>
        (openingRegularGamma a b η t - Gamma a b) / t +
          lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b
            (Fin.last r) * (spectralAtom (t ^ 2) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Gamma_opening_eq_regular_add]
    field_simp [ht.ne']
    ring
  simpa using hsum.congr' heq.symm
end MetricCodes.Spherical.HigherHierarchy
