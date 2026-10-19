-- Prove2me | solution 1 for MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/3912df33-34bd-498e-99e5-4ae76f5650f8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_localizedEnvelope_bddBelow

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
noncomputable section
open scoped InnerProductSpace Topology
open MetricCodes.Spherical.SidelnikovLocalization
namespace MetricCodes.Spherical.SidelnikovLocalization
theorem _root_.solution {κ : ℝ → ℝ} {s t : ℝ}
    (hs : s < 1) (ht : t ∈ Set.Icc (0 : ℝ) s)
    (hκ : ∀ x ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ x) :
    localizedEnvelope κ s ≤ κ t + sliceCost s t := by
  exact csInf_le (localizedEnvelope_bddBelow hs hκ)
    ⟨t, ht, rfl⟩
end MetricCodes.Spherical.SidelnikovLocalization
