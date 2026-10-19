-- Prove2me | solution 1 for MetricCodes.card_hammingSphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/72af2f98-e469-483f-9cc5-5e59c7183499

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryTranslate_injective
import Theorems.Thm_MetricCodes_card_weightShell
import Theorems.Thm_MetricCodes_hammingSphere_eq_image

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    (hammingSphere x r).card = n.choose r := by
  rw [hammingSphere_eq_image,
    Finset.card_image_of_injective _ (binaryTranslate_injective x),
    card_weightShell]
end MetricCodes
