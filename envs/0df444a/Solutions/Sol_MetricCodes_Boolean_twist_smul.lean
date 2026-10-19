-- Prove2me | solution 1 for MetricCodes.Boolean.twist_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/554c9a49-b3c6-43e5-bfb3-c396fe6407d3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution (x : BinaryWord n) (c : ℝ) (f : Function n) :
    twist x (c • f) = c • twist x f := by
  funext S
  simp [twist, mul_left_comm]
end MetricCodes.Boolean
