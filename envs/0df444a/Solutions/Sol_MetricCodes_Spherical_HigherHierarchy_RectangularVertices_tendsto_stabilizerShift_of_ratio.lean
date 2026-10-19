-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_stabilizerShift_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/18ae4070-a825-4bdb-b41f-18b91c553024

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self

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
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r : ℕ}
    (mu : ℕ → Fin r → ℕ)
    (b : Fin r → ℝ) (i : Fin r)
    (hlim : Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i))) :
    Tendsto (fun n : ℕ => stabilizerShift n (mu n) i / (n : ℝ))
      atTop (𝓝 (b i + (1 / 2 : ℝ))) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hone := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hrow :=
    tendsto_const_div_atTop_nhds_zero_nat ((i.val : ℝ) + 1)
  convert
    (hlim.add ((hdimension.sub hone).div_const (2 : ℝ))).sub hrow
      using 1
  · ext n
    simp only [stabilizerShift, div_eq_mul_inv]
    ring
  · ring_nf
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
