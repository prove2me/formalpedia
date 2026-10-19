-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedEscapingRatioProduct_eq_filtered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/0ef52310-3662-489d-9290-05cefe907203

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
theorem _root_.solution
    {r k j : ℕ} (hkj : k + j = r) (d : Fin r → ℝ) :
    compactifiedEscapingRatioProduct hkj d =
      ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i := by
  classical
  subst r
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
