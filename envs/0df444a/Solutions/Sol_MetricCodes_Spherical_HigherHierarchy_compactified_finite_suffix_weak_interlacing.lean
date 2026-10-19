-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_finite_suffix_weak_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/fa0f215e-68a6-4b36-b1ad-fa826059d7a3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyTuple_recovered_weak_interlacing

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
open Set Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r k j : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (hA : ∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1)
    (hB : ∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1)
    (hinter : ∀ i : Fin j,
      compactifiedAmbientSuffix hkj A i.castSucc ≤
        compactifiedStabilizerSuffix hkj B i ∧
      compactifiedStabilizerSuffix hkj B i ≤
        compactifiedAmbientSuffix hkj A i.succ) :
    WeakInterlacing
      (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
      (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) :=
  compactifiedHierarchyTuple_recovered_weak_interlacing hA hB hinter
end MetricCodes.Spherical.HigherHierarchy
