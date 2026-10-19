-- Prove2me | solution 1 for MetricCodes.Boolean.raiseAt_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/de85d888-c9df-43ac-ad6a-ab763d9f076b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_character_erase

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
    raiseAt a (twist x f) =
      sign (x a) • twist x (raiseAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [raiseAt, ha, ite_true, twist,
      Pi.smul_apply, smul_eq_mul]
    rw [character_erase x a S ha]
    calc
      character x (S.erase a) * f (S.erase a) =
          (sign (x a) * sign (x a)) *
            (character x (S.erase a) * f (S.erase a)) := by
        rw [sign_mul_self, one_mul]
      _ = sign (x a) *
          ((sign (x a) * character x (S.erase a)) *
            f (S.erase a)) := by
        ring
  · simp [raiseAt, ha, twist]
end MetricCodes.Boolean
