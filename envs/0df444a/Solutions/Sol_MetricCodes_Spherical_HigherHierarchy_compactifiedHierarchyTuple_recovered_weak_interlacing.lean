-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedHierarchyTuple_recovered_weak_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/d286ba91-2c1b-47bf-9c69-321df6d42fd8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_recovered_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_recovered_antitone

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
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (hA : ∀ i, A i ∈ Set.Ioc (0 : ℝ) 1)
    (hB : ∀ i, B i ∈ Set.Ioc (0 : ℝ) 1)
    (hinter : ∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ) :
    0 ≤ (A (Fin.last r))⁻¹ - 1 ∧
      ∀ i : Fin r,
        (B i)⁻¹ - 1 ≤ (A i.castSucc)⁻¹ - 1 ∧
          (A i.succ)⁻¹ - 1 ≤ (B i)⁻¹ - 1 := by
  constructor
  · exact compactifiedHierarchyCoordinate_recovered_nonneg
      (hA (Fin.last r)).1 (hA (Fin.last r)).2
  · intro i
    exact ⟨compactifiedHierarchyCoordinate_recovered_antitone
      (hA i.castSucc).1 (hB i).1 (hinter i).1,
      compactifiedHierarchyCoordinate_recovered_antitone
        (hB i).1 (hA i.succ).1 (hinter i).2⟩
end MetricCodes.Spherical.HigherHierarchy
