-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_apply
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:03:49.964416+00:00
-- url     : https://prove2.me/submissions/054ae93d-353a-4208-81b1-9097ff54a7aa

import Mathlib
import Definitions.Def_OAIQ039C068

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

lemma matrixTrace_apply_oai (T : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ T=(Fintype.card ι : ℂ)⁻¹ * ∑ i,
      τ ⟨entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
        (mem_matrixVonNeumann ι i₀ M T).mp T.property i i⟩ := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm T)=_
  rw [MatrixGNS.trace_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  exact matrixEquiv_symm_entry ι i₀ M T i i

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_apply_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_apply_oai.{u_1, u_2}
