-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_lt_of_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/f850400e-182c-4494-9a45-50f33d84f4d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_localizedEnvelope_le

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
    {κ κ' : ℝ → ℝ} {s t : ℝ}
    (hs : s < 1) (ht : t ∈ Set.Icc (0 : ℝ) s)
    (hκ' : ∀ x ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ' x)
    (hmin : MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
      κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : κ' t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  calc
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s ≤
        κ' t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t :=
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_le hs ht hκ'
    _ < κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
      linarith
    _ = MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s :=
      hmin.symm
end MetricCodes.Spherical.HigherHierarchy
