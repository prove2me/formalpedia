-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixInclusion_commutes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:01.520711+00:00
-- url     : https://prove2.me/submissions/31089fff-0a8c-4d18-b984-8180e4b071da

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C063
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_entry

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCommute
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicColumns

variable {A ι H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instDecidableEq_solutions_1_rb64251_1 : DecidableEq ι := Classical.decEq ι
lemma diagonal_commutes_matrixRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (X : CStarMatrix ι ι A)
    (hT : ∀ i j,T*σ (X i j)=σ (X i j)*T) :
    OperatorAmplification.diagonal (H:=H) ι T*matrixRepresentation σ X=
      matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T := by
  ext v i
  simp only [mul_apply_eq_comp,OperatorAmplification.diagonal_apply,matrixRepresentation,
    StarAlgHom.coe_mk,matrixAction_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun R : H →L[ℂ] H => R (v j)) (hT i j)

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteMatrixSmallCorner
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

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_2
lemma matrixInclusion_commutes_oai (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
      ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
    (X : matrixVonNeumann ι i₀ Q) :
    diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ (matrixInclusion ι i₀ M Q hQM X)=
      CyclicColumns.matrixRepresentation ρ (matrixInclusion ι i₀ M Q hQM X)*diagonal (H:=K) ι T := by
  apply CyclicColumns.diagonal_commutes_matrixRepresentation
  intro i j
  let q : Q := ⟨entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j,
    (mem_matrixVonNeumann ι i₀ Q X).mp X.property i j⟩
  have he : matrixInclusion ι i₀ M Q hQM X i j=NormalSubalgebra.inclusion M Q hQM q := by
    apply Subtype.ext
    exact matrixInclusion_entry ι i₀ M Q hQM X i j
  rw [he]
  exact hT q

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrixInclusion_commutes_oai := @OAI.Kadison.OperatorAmplification.matrixInclusion_commutes_oai
