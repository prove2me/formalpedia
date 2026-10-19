-- Prove2me | solution 1 for MetricCodes.Spherical.HigherChannel.signedNode_denominator_neg_eq_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/fc243d64-db9f-4e73-a4e7-6c4520aea3ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_signedNode_denominator_neg
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_activeQuadraticDenominator_eq_prod_erase

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
open scoped BigOperators
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherChannel
theorem _root_.solution {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, false),
      (-L ℓ - signedNode L z)) = -activeDenominator L ℓ := by
  rw [signedNode_denominator_neg, activeDenominator,
    activeQuadraticDenominator_eq_prod_erase]
end MetricCodes.Spherical.HigherChannel
