-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.interlacing_paired_degree_ratio_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/fc5d60c2-8559-4241-8c64-b8b4be8ebcc2

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    b i / a i.castSucc ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : 0 < b i := h.stabilizer_pos i
  have ha : 0 < a i.castSucc := hb.trans (h.2 i).1
  constructor
  · exact div_nonneg hb.le ha.le
  · exact (div_le_one ha).2 (h.2 i).1.le
end MetricCodes.Spherical.HigherHierarchy
