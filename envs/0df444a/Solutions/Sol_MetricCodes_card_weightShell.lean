-- Prove2me | solution 1 for MetricCodes.card_weightShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/90b276c1-11cc-4179-b6fd-ea88657c122e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_wordOfSupport_injective
import Theorems.Thm_MetricCodes_weightShell_eq_image

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution (n w : ℕ) :
    (weightShell n w).card = n.choose w := by
  rw [weightShell_eq_image, Finset.card_image_of_injective _ wordOfSupport_injective,
    Finset.card_powersetCard]
  simp
end MetricCodes
