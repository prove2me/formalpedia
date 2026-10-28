-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:03:06.651507+00:00
-- url     : https://prove2.me/submissions/fb8e2328-54c4-4c66-913d-b2157bebd4e6

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_small_corner

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSRealCorner
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

namespace Kadison

lemma positive_re_le_nat_inv {z : ℂ} (hz : 0≤z) (n : ℕ)
    (h : z.re≤(n:ℝ)⁻¹) : z≤(n:ℂ)⁻¹ := by
  rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,←Complex.ofReal_inv]
  exact ⟨h,hz.2.symm⟩

namespace OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_4
variable (τ : M →ₚ[ℂ] ℂ)

theorem matrixGNSOperator_small_real_corner_oai (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : (MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)).re≤(Fintype.card ι : ℝ)⁻¹)
    (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖ ≤ c*‖X‖ := by
  apply matrixGNSOperator_small_corner ι i₀ M Q hQM τ hQ hτ hfaith h1 T hTQ hc hbound f hf _ X hX
  exact positive_re_le_nat_inv
    ((MatrixGNS.trace (ι:=ι) τ).map_nonneg ((hf.map (matrixInclusion ι i₀ M Q hQM)).nonneg))
    (Fintype.card ι) htrace

end OperatorAmplification

end Kadison

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner_oai := @OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner_oai
