-- Prove2me | solution 1 for MetricCodes.card_translateLocalizedCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/c365d352-f628-46cc-ab42-7b04588b7d22

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryTranslate_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    (translateLocalizedCode C z w).card = (localizedCode C z w).card := by
  exact Finset.card_image_of_injective _ (binaryTranslate_injective z)
end MetricCodes
