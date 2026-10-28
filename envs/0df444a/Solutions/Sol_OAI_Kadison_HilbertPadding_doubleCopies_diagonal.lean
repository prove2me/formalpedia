-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.doubleCopies_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:24:53.016212+00:00
-- url     : https://prove2.me/submissions/766d3894-0da6-4a82-88c0-9a2612b3b66f

import Mathlib
import Definitions.Def_OAIQ039C027

section
-- module Solutions.OAIQ039_CM.Commutator_DoubleCopies
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

variable (ι : Type*) [Fintype ι]

local instance doubleCopiesIndexDecidableEq_r940cd3_1 : DecidableEq ι := Classical.decEq ι
lemma doubleCopies_diagonal_oai (a : H →L[ℂ] H) :
    (diagonal (H:=H) ((Fin 2)×ι) a).comp (doubleCopies (H:=H) ι).toContinuousLinearMap=
      (doubleCopies (H:=H) ι).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v p
  simp only [comp_apply,diagonal_apply,LinearIsometry.coe_toContinuousLinearMap,doubleCopies_apply]
  by_cases h : p.1=0 <;> simp [h]

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.HilbertPadding.doubleCopies_diagonal_oai.{u_1, u_2} := @OAI.Kadison.HilbertPadding.doubleCopies_diagonal_oai.{u_1, u_2}
