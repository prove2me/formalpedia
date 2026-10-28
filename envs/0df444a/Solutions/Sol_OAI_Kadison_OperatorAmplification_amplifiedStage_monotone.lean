-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.amplifiedStage_monotone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:00:45.899986+00:00
-- url     : https://prove2.me/submissions/123899c7-fee1-405e-b118-758c8461bbd1

import Mathlib
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_diagonal

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
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

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : MatrixTower.Stage M)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq
lemma amplifiedStage_scalar (a : Matrix ι ι ℂ) :
    scalarMatrixHom ι i₀ M a∈(amplifiedStage ι i₀ M E).hom.range := by
  have hh := MatrixTensor.left_mem (A := matrixVonNeumann ι i₀ M)
    (I := ι) (J := E.I) (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y)) a
  obtain ⟨b,hb⟩ := hh
  exact ⟨b,hb⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTensorRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixTensor

variable {A I J : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hc : ∀ x y,Commute (φ x) (ψ y))

lemma range_le (S : StarSubalgebra ℂ A) (hφ : φ.range≤S) (hψ : ψ.range≤S) :
    (representation φ ψ hc).range≤S := by
  rintro a ⟨x,rfl⟩
  change (∑ i,∑ j,x i j • (φ (Matrix.single i.1 j.1 1)*ψ (Matrix.single i.2 j.2 1)))∈S
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  exact S.smul_mem (S.mul_mem (hφ ⟨_,rfl⟩) (hψ ⟨_,rfl⟩)) _

end Kadison.MatrixTensor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerGeometry
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

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : ℕ → MatrixTower.Stage M)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerGeometryIndexDecidableEq
lemma amplifiedStage_monotone_oai (hE : Monotone (fun n => (E n).hom.range)) :
    Monotone (fun n => (amplifiedStage ι i₀ M (E n)).hom.range) := by
  intro n m h
  apply MatrixTensor.range_le (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp (E n).hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x ((E n).hom y))
    ((amplifiedStage ι i₀ M (E m)).hom.range)
  · rintro a ⟨b,rfl⟩
    exact amplifiedStage_scalar ι i₀ M (E m) b
  · rintro a ⟨b,rfl⟩
    obtain ⟨c,hc⟩ := hE h (show (E n).hom b∈(E n).hom.range from ⟨b,rfl⟩)
    change diagonalHom ι i₀ M ((E n).hom b)∈_
    rw [←hc]
    exact amplifiedStage_diagonal ι i₀ M (E m) c

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.amplifiedStage_monotone_oai := @OAI.Kadison.OperatorAmplification.amplifiedStage_monotone_oai
