-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:04:33.877733+00:00
-- url     : https://prove2.me/submissions/d458567e-80f8-4fbb-8b20-39744a23663f

import Mathlib
import Definitions.Def_OAIQ039C062
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_apply

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuseTransfer
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

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq
lemma entry_diagonal (a : H →L[ℂ] H) (i : ι) :
    entry ι (diagonal (H:=H) ι a) i i=a := by
  ext x
  simp only [entry_apply,diagonal_single,single_apply,ite_true]

lemma matrixTrace_diagonal_oai (τ : M →ₚ[ℂ] ℂ) (a : M) :
    matrixTrace ι i₀ M τ (diagonalHom ι i₀ M a)=τ a := by
  rw [matrixTrace_apply]
  have he (i : ι) : (⟨entry ι ((diagonalHom ι i₀ M a):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
    (mem_matrixVonNeumann ι i₀ M _).mp (diagonalHom ι i₀ M a).property i i⟩:M)=a := by
    apply Subtype.ext
    exact entry_diagonal ι (a:H →L[ℂ] H) i
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  let : Nonempty ι := ⟨i₀⟩
  rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=ι)),one_mul]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_diagonal_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_diagonal_oai.{u_1, u_2}
