-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.rightCopies_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:27:07.236859+00:00
-- url     : https://prove2.me/submissions/c361b535-6ff9-45b1-a26b-0da91638c5c8

import Mathlib
import Definitions.Def_OAIQ039C027

section
-- module Solutions.OAIQ039_CM.Commutator_RightCopies
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance rightCopiesSourceDecidableEq_r109e7b_1 : DecidableEq ι := Classical.decEq ι
local instance rightCopiesPaddingDecidableEq_r109e7b_1 : DecidableEq κ := Classical.decEq κ
lemma rightCopies_diagonal_oai (a : H →L[ℂ] H) :
    (diagonal (H:=H) (κ⊕ι) a).comp (rightCopies (H:=H) ι κ).toContinuousLinearMap=
      (rightCopies (H:=H) ι κ).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v i
  cases i <;> simp

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.HilbertPadding.rightCopies_diagonal_oai.{u_1, u_2, u_3} := @OAI.Kadison.HilbertPadding.rightCopies_diagonal_oai.{u_1, u_2, u_3}
