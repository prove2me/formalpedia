-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:02:01.436267+00:00
-- url     : https://prove2.me/submissions/cfadcab8-0632-48e8-ad67-6bbc06d33846

import Mathlib
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_commutator_norm
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_restrict
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrix_small_corner_bound

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSCornerBound
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

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3
variable (τ : M →ₚ[ℂ] ℂ)

theorem matrixGNSOperator_small_corner_oai (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)≤(Fintype.card ι : ℂ)⁻¹)
    (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖ ≤ c*‖X‖ := by
  apply (matrixGNSOperator_commutator_norm ι M τ T X).le.trans
  rw [matrixTrace_restrict] at htrace
  exact matrix_small_corner_bound ι i₀ M Q hQM hQ (NormalSubalgebra.trace M Q hQM τ)
    (NormalSubalgebra.tracial M Q hQM τ hτ) (NormalSubalgebra.faithful M Q hQM τ hfaith)
    (NormalSubalgebra.one M Q hQM τ h1) ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom)
    T hTQ hc hbound f hf htrace X hX

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner_oai := @OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner_oai
