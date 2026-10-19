-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.interlacing_strictAnti_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/a60a010a-a744-4993-b47d-b4ccaf3c9f7c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : StrictAnti b := by
  cases r with
  | zero => exact fun i => Fin.elim0 i
  | succ r =>
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have hlow := (h.2 i.succ).1
      have hhigh := (h.2 i.castSucc).2
      have hindex : i.succ.castSucc = i.castSucc.succ := by
        apply Fin.ext
        simp
      rw [hindex] at hlow
      exact hlow.trans hhigh
end MetricCodes.Spherical.HigherHierarchy
