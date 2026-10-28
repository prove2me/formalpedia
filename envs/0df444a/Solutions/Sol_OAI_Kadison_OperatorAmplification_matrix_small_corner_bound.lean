-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrix_small_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:59.092103+00:00
-- url     : https://prove2.me/submissions/9e8147fa-a3bf-4f64-a253-a26a491595b8

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_CornerTransport_finite_small_corner_bound
import Theorems.Thm_OAI_Kadison_MatrixGNS_rowMatrix_trace
import Theorems.Thm_OAI_Kadison_MatrixGNS_row_corner_commutator_bound
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_commutes
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_row
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_faithful
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_tracial

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVonNeumann
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

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

lemma factor_matrixVonNeumann (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M) :
    FactorCorner.IsFactor (matrixVonNeumann ι i₀ M) := by
  intro Z hZ hc
  have he : Z=diagonal (H:=H) ι (entry ι Z i₀ i₀) :=
    diagonal_of_matrixUnits ι i₀ Z (fun i j => hc _ (matrixUnit_mem ι i₀ M i j))
  have ha := (mem_matrixVonNeumann ι i₀ M Z).mp hZ i₀ i₀
  have hca : entry ι Z i₀ i₀∈Set.centralizer (M:Set (H →L[ℂ] H)) := by
    intro a ha
    exact entry_commutes ι Z a (hc _ (diagonal_mem_matrixVonNeumann ι i₀ M ha)) i₀ i₀
  obtain ⟨c,hc⟩ := hM _ ha hca
  refine ⟨c,?_⟩
  rw [he,hc,map_smul,map_one]

end Kadison.OperatorAmplification

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

lemma matrixTrace_equiv (X : CStarMatrix ι ι M) :
    matrixTrace ι i₀ M τ (matrixEquiv ι i₀ M X)=MatrixGNS.trace (ι:=ι) τ X := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (matrixEquiv ι i₀ M X))=_
  rw [StarAlgEquiv.symm_apply_apply]

end Kadison.OperatorAmplification

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
lemma rowMatrix_mul (i : ι) (a b : A) : rowMatrix i a*rowMatrix i b=rowMatrix i (a*b) := by
  ext j k
  simp only [CStarMatrix.mul_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

omit [Fintype ι] in
lemma rowMatrix_star (i : ι) (a : A) : star (rowMatrix i a)=rowMatrix i (star a) := by
  ext j k
  simp only [CStarMatrix.star_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

lemma rowMatrix_projection (i : ι) : IsStarProjection (rowMatrix i (1:A)) := by
  constructor
  · change rowMatrix i (1:A)*rowMatrix i (1:A)=rowMatrix i 1
    rw [rowMatrix_mul,one_mul]
  · change star (rowMatrix i (1:A))=rowMatrix i 1
    rw [rowMatrix_star,star_one]

end Kadison.MatrixGNS

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
theorem matrix_small_corner_bound_oai (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0) (h1 : σ 1=1)
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
      ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ a : M,‖T*ρ a-ρ a*T‖ ≤ c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : matrixTrace ι i₀ Q σ f≤(Fintype.card ι : ℂ)⁻¹)
    (X : CStarMatrix ι ι M)
    (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ X-
      CyclicColumns.matrixRepresentation ρ X*diagonal (H:=K) ι T‖ ≤ c*‖X‖ := by
  let e : matrixVonNeumann ι i₀ Q := matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i₀ (1:Q))
  have he : IsStarProjection e :=
    (MatrixGNS.rowMatrix_projection (A:=Q) i₀).map (matrixEquiv ι i₀ Q).toStarAlgHom
  have hje : matrixInclusion ι i₀ M Q hQM e=MatrixGNS.rowMatrix i₀ (1:M) :=
    matrixInclusion_row ι i₀ M Q hQM i₀
  have hte : matrixTrace ι i₀ Q σ e=(Fintype.card ι : ℂ)⁻¹ := by
    change matrixTrace ι i₀ Q σ (matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i₀ (1:Q)))=_
    rw [matrixTrace_equiv,MatrixGNS.rowMatrix_trace σ h1]
  refine CornerTransport.finite_small_corner_bound (matrixVonNeumann ι i₀ Q)
    (factor_matrixVonNeumann ι i₀ Q hQ) (matrixTrace ι i₀ Q σ)
    (matrixTrace_tracial ι i₀ Q σ hσ) (matrixTrace_faithful ι i₀ Q σ hfaith)
    (matrixInclusion ι i₀ M Q hQM) (CyclicColumns.matrixRepresentation ρ)
    (diagonal (H:=K) ι T) (matrixInclusion_commutes ι i₀ M Q hQM ρ T hT)
    e he ?_ f hf (by rw [hte]; exact htrace) X hX
  intro Z hZ
  rw [hje] at hZ
  exact MatrixGNS.row_corner_commutator_bound ρ T hc hbound i₀ Z hZ

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrix_small_corner_bound_oai := @OAI.Kadison.OperatorAmplification.matrix_small_corner_bound_oai
