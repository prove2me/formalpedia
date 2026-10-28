-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.rowMatrix_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:38:40.982598+00:00
-- url     : https://prove2.me/submissions/479a21b9-f374-470f-ae05-b2614aca026c

import Mathlib
import Definitions.Def_OAIQ039C061

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
-- module Solutions.OAIQ039_CM.Commutator_MatrixRowCorner
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

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixRowCornerDecidableEq
variable [PartialOrder A] [StarOrderedRing A]

lemma rowMatrix_trace_oai (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (i : ι) :
    trace (ι:=ι) τ (rowMatrix i (1:A))=(Fintype.card ι : ℂ)⁻¹ := by
  rw [trace_apply]
  simp [rowMatrix_apply,apply_ite,h1]

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixGNS.rowMatrix_trace_oai.{u_1, u_2} := @OAI.Kadison.MatrixGNS.rowMatrix_trace_oai.{u_1, u_2}
