-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_lagrangeWeight_prepend_scale_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/0c8701a6-e4af-4995-8e7f-233ee6f5a94b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_prepend_succ
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_retainedQuadraticResidueFactor_atTop

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (c : ℝ) (i : Fin (r + 1)) :
    Tendsto
      (fun u : ℝ =>
        lagrangeWeight (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) i.succ)
      atTop (𝓝 (c ^ 2 * lagrangeWeight a b i)) := by
  have hfactor :=
    tendsto_retainedQuadraticResidueFactor_atTop (a i) c
  have hlimit :
      Tendsto
        (fun u : ℝ => lagrangeWeight a b i *
          ((quadraticCoordinate (a i) - c ^ 2 * quadraticCoordinate u) /
            (quadraticCoordinate (a i) - quadraticCoordinate u)))
        atTop (𝓝 (c ^ 2 * lagrangeWeight a b i)) := by
    simpa [mul_comm] using hfactor.const_mul (lagrangeWeight a b i)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (max 0 (a i))] with u hu
  have hu0 : 0 < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hau : a i < u := lt_of_le_of_lt (le_max_right _ _) hu
  have hquad : quadraticCoordinate (a i) < quadraticCoordinate u :=
    quadraticCoordinate_strictMonoOn (h.ambient_nonneg i) hu0.le hau
  have hne : quadraticCoordinate (a i) - quadraticCoordinate u ≠ 0 := by
    linarith
  rw [lagrangeWeight_prepend_succ h u
    (scaleCoordinate (c ^ 2) u) i hne,
    quadraticCoordinate_scaleCoordinate (sq_nonneg c) hu0.le]
end MetricCodes.Spherical.HigherHierarchy
