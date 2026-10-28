-- Prove2me | solution 1 for OAI.Kadison.BiprodLinkColumn.compression_empty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:21:46.443732+00:00
-- url     : https://prove2.me/submissions/04282196-f566-4b27-a852-941615f6be63

import Mathlib
import Definitions.Def_OAIQ039C020

section
-- module Solutions.OAIQ039_CM.Commutator_BiprodLinkEmpty
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G)) (S : Set (Intertwiner N))

lemma compression_empty_oai : compression N S ∅=0 := by
  simp only [compression,finiteProjection,Finset.sum_empty,ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero]

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.BiprodLinkColumn.compression_empty_oai.{u_1, u_2} := @OAI.Kadison.BiprodLinkColumn.compression_empty_oai.{u_1, u_2}
