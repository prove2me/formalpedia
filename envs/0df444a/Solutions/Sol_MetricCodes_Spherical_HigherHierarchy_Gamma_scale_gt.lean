-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_scale_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/03334edc-29b0-4c29-945f-be97b2f8cdf4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_scale_lt

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
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    {c : ℝ} (hc : 1 < c) :
    Gamma a b < Gamma (scaleAmbient c a) (scaleStabilizer c b) := by
  unfold Gamma
  apply Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r + 1))).Nonempty)
  intro i _
  rw [lagrangeWeight_scale h (by linarith) i]
  apply mul_lt_mul_of_pos_left _ (h.lagrangeWeight_pos i)
  exact spectralAtom_scale_lt hc
    (hlast.trans_le (h.strictAnti_ambient.antitone i.le_last))
end MetricCodes.Spherical.HigherHierarchy
