-- Prove2me | solution 1 for MetricCodes.Boolean.character_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/d4ed9f05-7801-45b5-8ff0-8f74e314608f

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
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) :
    character x S = sign (x a) * character x (S.erase a) := by
  have h := character_insert x a (S.erase a)
    (by simp)
  simpa [Finset.insert_erase ha] using h
end MetricCodes.Boolean
