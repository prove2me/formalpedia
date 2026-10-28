-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.norm_padMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:16:11.701412+00:00
-- url     : https://prove2.me/submissions/d6528dd3-e49d-4c21-aef0-5d6d14266f3a

import Mathlib
import Definitions.Def_OAIQ039C012

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixPadding
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

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixPaddingSourceDecidableEq_re83567_1 : DecidableEq ι := Classical.decEq ι
local instance matrixPaddingComplementDecidableEq_re83567_1 : DecidableEq κ := Classical.decEq κ
lemma norm_padMatrix_le_oai (X : CStarMatrix ι ι A) : ‖padMatrix ι κ X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (padMatrix ι κ) X

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_3, u_4} : type_of% @OAI.Kadison.HilbertPadding.norm_padMatrix_le_oai.{u_1, u_3, u_4} := @OAI.Kadison.HilbertPadding.norm_padMatrix_le_oai.{u_1, u_3, u_4}
