-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeWeight_append_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/a13b4f7b-2ab9-4c0c-b4c7-569c7e4041f0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeDenominator_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeNumerator_append_castSucc
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeDenominator_append_castSucc

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
    (ε : ℝ) (i : Fin (r + 1)) :
    lagrangeWeight (appendAmbient a) (appendStabilizer b ε) i.castSucc =
      lagrangeWeight a b i *
        (1 - quadraticCoordinate ε / quadraticCoordinate (a i)) := by
  have hai : 0 < a i :=
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hquad : quadraticCoordinate (a i) ≠ 0 := by
    unfold quadraticCoordinate
    positivity
  have hden : lagrangeDenominator a i ≠ 0 :=
    h.lagrangeDenominator_ne_zero i
  unfold lagrangeWeight
  rw [lagrangeNumerator_append_castSucc,
    lagrangeDenominator_append_castSucc]
  field_simp [hquad, hden]
end MetricCodes.Spherical.HigherHierarchy
