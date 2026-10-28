-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_restrict
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:06:03.035129+00:00
-- url     : https://prove2.me/submissions/4aa82a62-03a7-4a95-ae9c-5e2ab541683c

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_entry
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_apply

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVectorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

lemma diagonal_inner (X : CStarMatrix ι ι A) :
    inner ℂ (algebraArray τ (1:CStarMatrix ι ι A)) (algebraArray τ X)=∑ i,τ (X i i) := by
  simp only [PiLp.inner_apply,algebraArray_apply,TracialGNS.inner_algebraVector,CStarMatrix.one_apply]
  simp [apply_ite]

lemma trace_apply (X : CStarMatrix ι ι A) :
    trace (ι:=ι) τ X=(Fintype.card ι : ℂ)⁻¹ * ∑ i,τ (X i i) := by
  rw [trace_vector,representation_vacuum,vacuum,inner_smul_left,inner_smul_right,diagonal_inner]
  have hs : starRingEnd ℂ (scale ι)*scale ι=(Fintype.card ι : ℂ)⁻¹ := by
    change star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)=_
    rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,←mul_inv_rev,
      Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [←mul_assoc,hs]

end Kadison.MatrixGNS

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
lemma matrixTrace_restrict_oai (τ : M →ₚ[ℂ] ℂ) (X : matrixVonNeumann ι i₀ Q) :
    MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM X)=
      matrixTrace ι i₀ Q (NormalSubalgebra.trace M Q hQM τ) X := by
  rw [MatrixGNS.trace_apply,matrixTrace_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [NormalSubalgebra.trace_apply]
  congr 1
  apply Subtype.ext
  exact matrixInclusion_entry ι i₀ M Q hQM X i i

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_restrict_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_restrict_oai.{u_1, u_2}
