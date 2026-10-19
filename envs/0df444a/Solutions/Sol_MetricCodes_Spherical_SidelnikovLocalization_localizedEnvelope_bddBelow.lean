-- Prove2me | solution 1 for MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/3e1400a2-3fe9-453e-8686-b35c3112beb6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_sliceCost_nonneg

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
theorem _root_.solution {κ : ℝ → ℝ} {s : ℝ}
    (hs : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t) :
    BddBelow ((fun t => κ t + sliceCost s t) '' Set.Icc 0 s) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact add_nonneg (hκ t ht) (sliceCost_nonneg ht.2 hs)
end MetricCodes.Spherical.SidelnikovLocalization
