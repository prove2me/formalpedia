-- Prove2me | solution 1 for MetricCodes.hammingDist_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/8f82b9be-488d-490c-9972-412f839e3f0d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x y : BinaryWord n) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp [ne_comm]
end MetricCodes
