-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_scale_sub_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/9aef111f-780e-4cd0-a6c2-865c99f0aa66

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_scale_sub_lower_bound

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
    (h : Interlacing a b) {c : ℝ}
    (hc : 1 ≤ c) (hc' : c ≤ 2) :
    (c - 1) * scalingGainCoefficient a b ≤
      Gamma (scaleAmbient c a) (scaleStabilizer c b) - Gamma a b := by
  unfold Gamma scalingGainCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [lagrangeWeight_scale h (by linarith) i]
  have hbound := spectralAtom_scale_sub_lower_bound
    hc hc' (h.ambient_nonneg i)
  have hweighted := mul_le_mul_of_nonneg_left hbound
    (h.lagrangeWeight_nonneg i)
  dsimp [scaleAmbient]
  convert hweighted using 1 <;> ring
end MetricCodes.Spherical.HigherHierarchy
