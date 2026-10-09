-- Prove2me | solution 1 for OAI.Erdos3.affineComparisonMoment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:16.40472+00:00
-- url     : https://prove2.me/submissions/82818df4-9fd1-4aa0-87eb-3cde6fb19f72

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonMoment_bounds {P : ℝ} (hP : 0 ≤ P) :
    2 ≤ affineComparisonMoment P ∧ Even (affineComparisonMoment P) ∧
    P ≤ (affineComparisonMoment P : ℝ) ∧ (affineComparisonMoment P : ℝ) ≤ P + 2 := by
  unfold affineComparisonMoment
  refine ⟨by omega, even_two_mul _, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (P / 2)
    push_cast
    linarith
  · have h := Nat.floor_le (by positivity : 0 ≤ P / 2)
    push_cast
    linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.affineComparisonMoment_bounds := @OAI.Erdos3.affineComparisonMoment_bounds
