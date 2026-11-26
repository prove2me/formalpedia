-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstJumpClockAttainedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:50.90999+00:00
-- url     : https://prove2.me/submissions/01d3ddb5-825b-42bc-9b5b-411352966f6b

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Order.LeftRightLim
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → Real) (a : NNReal) (ha : 0 < a)
    (hJump : f a - Function.leftLim f a < 0)
    (hBefore : ∀ t : NNReal, 0 < t → t < a → f t = Function.leftLim f t) :
    (⨅ t : NNReal, if 0 < t ∧ f t - Function.leftLim f t < 0
      then (t : WithTop NNReal) else ⊤) = (a : WithTop NNReal) := by
  apply le_antisymm
  · simpa [ha,hJump] using
      (iInf_le (fun t : NNReal => if 0 < t ∧ f t - Function.leftLim f t < 0
        then (t : WithTop NNReal) else ⊤) a)
  · apply le_iInf
    intro t
    split
    · rename_i ht
      exact_mod_cast le_of_not_gt (fun h => by
        rw [hBefore t ht.1 h, sub_self] at ht
        exact (lt_irrefl (0 : Real)) ht.2)
    · exact le_top
