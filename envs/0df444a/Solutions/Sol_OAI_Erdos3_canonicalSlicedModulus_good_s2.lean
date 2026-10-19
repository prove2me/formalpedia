-- Prove2me | solution 1 for OAI.Erdos3.canonicalSlicedModulus_good_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:49:13.025007+00:00
-- url     : https://prove2.me/submissions/01297dd6-76d5-49c1-921e-74946fb58929

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_good_s2_oai (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) :
    canonicalSlicedModulus (M := M) selection stride height x =
      residueRefinedPeriod (kernelPeriodCandidate (height + 1)
        (goodKernelUniformCandidate selection x hx height)) stride := by
  simp only [canonicalSlicedModulus, dif_pos hx]

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.canonicalSlicedModulus_good_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.canonicalSlicedModulus_good_s2_oai.{u_1, u_2, u_3}
