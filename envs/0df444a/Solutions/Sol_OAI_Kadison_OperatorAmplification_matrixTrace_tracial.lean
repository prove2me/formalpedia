-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_tracial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:08.854825+00:00
-- url     : https://prove2.me/submissions/fa334e54-9668-4086-95fc-581ce7cc2bce

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_mul

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
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

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixTrace_tracial_oai (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (X Y : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ (X*Y)=matrixTrace ι i₀ M τ (Y*X) := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (X*Y))=
    MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (Y*X))
  simp only [map_mul]
  exact MatrixGNS.trace_mul (ι:=ι) τ hτ _ _

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_tracial_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_tracial_oai.{u_1, u_2}
