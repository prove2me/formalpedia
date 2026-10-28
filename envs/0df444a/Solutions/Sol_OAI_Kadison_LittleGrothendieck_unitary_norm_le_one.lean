-- Prove2me | solution 1 for OAI.Kadison.LittleGrothendieck.unitary_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:05:51.421072+00:00
-- url     : https://prove2.me/submissions/0df376db-73d8-4eaa-a8f6-0b18a9418df6

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_LittleGrothendieckSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.LittleGrothendieck

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma unitary_norm_le_one_oai (u : unitary A) : ‖(u:A)‖≤1 := by
  cases subsingleton_or_nontrivial A with
  | inl h => simpa only [Subsingleton.elim (u:A) 0,norm_zero] using (zero_le_one : (0:ℝ)≤1)
  | inr h => exact le_of_eq (CStarRing.norm_coe_unitary u)

end Kadison.LittleGrothendieck

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.LittleGrothendieck.unitary_norm_le_one_oai.{u_1} := @OAI.Kadison.LittleGrothendieck.unitary_norm_le_one_oai.{u_1}
