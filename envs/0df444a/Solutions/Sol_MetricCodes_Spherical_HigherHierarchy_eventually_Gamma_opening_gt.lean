-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_Gamma_opening_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/cbbbe437-279a-49b5-99bb-b3d951209f09

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_opening_slope
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_opening_spectralSlope_pos

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
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Gamma a b <
        Gamma
          (openingAmbient a (openingContractionSpeed a b * t) (t ^ 2)) b := by
  let η : ℝ := openingContractionSpeed a b
  have hlimit := tendsto_Gamma_opening_slope h hzero η
  have hpositive : 0 < η * deriv (openingRegularGamma a b 1) 0 +
      lagrangeWeight a b (Fin.last r) := opening_spectralSlope_pos h
  have hevent := hlimit.eventually (lt_mem_nhds hpositive)
  filter_upwards [hevent, self_mem_nhdsWithin]
    with t ht (htpos : 0 < t)
  have hdiff := (lt_div_iff₀ htpos).mp ht
  dsimp [η] at hdiff ⊢
  linarith
end MetricCodes.Spherical.HigherHierarchy
