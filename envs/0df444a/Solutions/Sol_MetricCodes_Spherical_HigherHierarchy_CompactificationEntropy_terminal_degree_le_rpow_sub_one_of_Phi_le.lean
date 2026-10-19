-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.terminal_degree_le_rpow_sub_one_of_Phi_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/d0573ec1-b5ba-4e60-aeb4-7158a6d6449c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_terminal_entropy_le_Phi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_degree_le_rpow_sub_one_of_sphericalEntropy_le

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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {C : ℝ} (hC : Phi a b ≤ C) :
    a (Fin.last r) ≤ (2 : ℝ) ^ C - 1 :=
  degree_le_rpow_sub_one_of_sphericalEntropy_le h.1
    ((terminal_entropy_le_Phi h).trans hC)
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
