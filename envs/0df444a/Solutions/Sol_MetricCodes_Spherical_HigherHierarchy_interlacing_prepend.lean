-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.interlacing_prepend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/dba01148-457f-43a4-a164-ec03406e694a

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
    (h : Interlacing a b) {u v : ℝ}
    (huv : v < u) (hva : a 0 < v) :
    Interlacing (prependAmbient u a) (prependStabilizer v b) := by
  constructor
  · simpa [prependAmbient] using h.1
  · intro i
    induction i using Fin.cases with
    | zero =>
        simpa [prependAmbient, prependStabilizer] using ⟨huv, hva⟩
    | succ i =>
        simpa [prependAmbient, prependStabilizer] using h.2 i
end MetricCodes.Spherical.HigherHierarchy
