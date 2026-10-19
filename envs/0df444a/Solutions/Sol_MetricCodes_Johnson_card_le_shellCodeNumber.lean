-- Prove2me | solution 1 for MetricCodes.Johnson.card_le_shellCodeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/ce2bc35c-7e55-46a7-8ffe-ec43c6193e00

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) (hC : IsBinaryCode d C) :
    C.card ≤ shellCodeNumber n w d := by
  exact Finset.le_sup ((mem_shellCodeFamily C).mpr ⟨hweight, hC⟩)
end MetricCodes.Johnson
