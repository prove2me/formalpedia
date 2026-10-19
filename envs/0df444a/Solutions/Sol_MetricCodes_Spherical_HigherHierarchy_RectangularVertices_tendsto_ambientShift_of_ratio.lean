-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_ambientShift_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/919e0fef-4235-4593-9761-97c8ee0e4f20

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
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1))
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto (fun n : ℕ => ambientShift n (lam n) i / (n : ℝ))
      atTop (𝓝 (a i + (1 / 2 : ℝ))) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hrow :=
    tendsto_const_div_atTop_nhds_zero_nat ((i.val : ℝ) + 1)
  convert (hlim.add (hdimension.div_const (2 : ℝ))).sub hrow using 1
  · ext n
    simp only [ambientShift, div_eq_mul_inv]
    ring
  · ring_nf
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
