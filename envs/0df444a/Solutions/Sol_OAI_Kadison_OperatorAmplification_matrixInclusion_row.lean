-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixInclusion_row
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:48:08.06123+00:00
-- url     : https://prove2.me/submissions/abc82ca7-aa13-4efe-ab1b-ac2f6a54de1d

import Mathlib
import Definitions.Def_OAIQ039C063
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_entry

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerInclusion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq
lemma matrixInclusion_row_oai (i : ι) :
    matrixInclusion ι i₀ M Q hQM (matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i (1:Q)))=
      MatrixGNS.rowMatrix i (1:M) := by
  apply CStarMatrix.ext
  intro j k
  apply Subtype.ext
  rw [matrixInclusion_entry]
  change entry ι (CyclicColumns.matrixRepresentation (A:=Q) (H:=H) Q.toStarSubalgebra.subtype
    (MatrixGNS.rowMatrix i (1:Q))) j k=_
  rw [entry_matrixRepresentation]
  simp only [MatrixGNS.rowMatrix_apply]
  split_ifs <;> rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixInclusion_row_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixInclusion_row_oai.{u_1, u_2}
