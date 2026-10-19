-- Prove2me | solution 1 for MetricCodes.Boolean.lowerAt_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/942872dd-9398-4589-a720-75250fa13526

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_character_insert

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (x : BinaryWord n) (a : Fin n) (f : Function n) :
    lowerAt a (twist x f) =
      sign (x a) • twist x (lowerAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp [lowerAt, ha, twist]
  · simp [lowerAt, ha, twist, character_insert x a S ha,
      mul_assoc]
end MetricCodes.Boolean
