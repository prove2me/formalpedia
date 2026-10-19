-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.interlacing_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/7dba41c2-140b-45db-9e11-e31281a29265

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε < a (Fin.last r)) :
    Interlacing (appendAmbient a) (appendStabilizer b ε) := by
  constructor
  · simp [appendAmbient]
  · intro i
    induction i using Fin.lastCases with
    | last =>
        simpa [appendAmbient, appendStabilizer] using ⟨hεa, hε⟩
    | cast i =>
        simpa [appendAmbient, appendStabilizer, ← Fin.castSucc_succ] using h.2 i
end MetricCodes.Spherical.HigherHierarchy
