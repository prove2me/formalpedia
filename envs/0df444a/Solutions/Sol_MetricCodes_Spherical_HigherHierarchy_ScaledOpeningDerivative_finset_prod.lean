-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ScaledOpeningDerivative.finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/1ad857ab-a528-421d-acac-55aab7c0be64

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
namespace ScaledOpeningDerivative
theorem _root_.solution {ι : Type*} {η : ℝ}
    (s : Finset ι) {f F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ScaledOpeningDerivative η (f i) (F i)) :
    ScaledOpeningDerivative η
      (fun t => ∏ i ∈ s, f i t)
      (fun t => ∏ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ScaledOpeningDerivative.const η 1
  | @insert i s hi ih =>
      simpa [Finset.prod_insert hi] using
        (h i (Finset.mem_insert_self _ _)).mul
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end ScaledOpeningDerivative
end MetricCodes.Spherical.HigherHierarchy
