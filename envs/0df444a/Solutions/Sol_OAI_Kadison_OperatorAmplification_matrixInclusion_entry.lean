-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixInclusion_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:24.030647+00:00
-- url     : https://prove2.me/submissions/8f7288c7-212d-452c-b4c5-fc79784e5de6

import Mathlib
import Definitions.Def_OAIQ039C063

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraEquiv
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

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions
lemma matrixEquiv_symm_entry (T : matrixVonNeumann ι i₀ M) (i j : ι) :
    ((matrixEquiv ι i₀ M).symm T i j:H →L[ℂ] H)=
      entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j := by
  rw [←entry_matrixRepresentation]
  have h := congrArg (fun X : matrixVonNeumann ι i₀ M =>
    entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j)
    ((matrixEquiv ι i₀ M).apply_symm_apply T)
  exact h

end Kadison.OperatorAmplification

end

end
end

end OAI
end

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
lemma matrixInclusion_entry_oai (X : matrixVonNeumann ι i₀ Q) (i j : ι) :
    (matrixInclusion ι i₀ M Q hQM X i j:H →L[ℂ] H)=
      entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j := by
  exact matrixEquiv_symm_entry ι i₀ M _ i j

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixInclusion_entry_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixInclusion_entry_oai.{u_1, u_2}
