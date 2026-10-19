-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedHierarchyTuple_terminal_limit_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/887cd56a-36ac-48ba-a85a-c4f61a372fb6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_terminal_degree_le_rpow_sub_one_of_Phi_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_limit_pos_of_bddAbove

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
theorem _root_.solution {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C)
    (hA : Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) (Fin.last r)))
      atTop (nhds (A (Fin.last r)))) :
    0 < A (Fin.last r) := by
  apply compactifiedHierarchyCoordinate_limit_pos_of_bddAbove
    (fun k => (h (φ k)).ambient_nonneg (Fin.last r))
    (C := (2 : ℝ) ^ C - 1)
  · exact fun k =>
      CompactificationEntropy.terminal_degree_le_rpow_sub_one_of_Phi_le
        (h (φ k)) (hbound (φ k))
  · exact hA
end MetricCodes.Spherical.HigherHierarchy
