-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedEscapingRatioProduct_eq_filtered_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/bfa92f77-efac-4dbf-b9d4-5d650d9c8724

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
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {R k j : ℕ} (hkj : k + j = R) (d : Fin R → ℝ) :
    compactifiedEscapingRatioProduct hkj d =
      ∏ i ∈ Finset.univ.filter (fun i : Fin R => i.val < k), d i := by
  classical
  subst R
  unfold compactifiedEscapingRatioProduct
  apply Finset.prod_bij
    (fun i _ => (i.castAdd j : Fin (k + j)))
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i₁ _ i₂ _ heq
    apply Fin.ext
    simpa using congrArg (fun z : Fin (k + j) => z.val) heq
  · intro i hi
    have hik : i.val < k := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hik⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl
end MetricCodes.Spherical.HigherHierarchy
