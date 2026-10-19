-- Prove2me | solution 1 for MetricCodes.Boolean.character_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/3c7e3e46-81d0-4384-9069-c8dd55c69c05

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
theorem _root_.solution
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∉ S) :
    character x (insert a S) = sign (x a) * character x S := by
  classical
  simp [character, ha]
end MetricCodes.Boolean
