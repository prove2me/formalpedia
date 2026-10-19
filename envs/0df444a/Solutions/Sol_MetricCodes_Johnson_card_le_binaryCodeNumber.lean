-- Prove2me | solution 1 for MetricCodes.Johnson.card_le_binaryCodeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/7a35ba67-c15e-4ea7-8b3e-3cf4cc034f91

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n d : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C) :
    C.card ≤ binaryCodeNumber n d := by
  exact Finset.le_sup ((mem_binaryCodeFamily C).mpr hC)
end MetricCodes.Johnson
