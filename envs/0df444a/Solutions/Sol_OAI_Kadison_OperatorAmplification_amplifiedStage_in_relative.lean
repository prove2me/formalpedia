-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.amplifiedStage_in_relative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:59:15.342271+00:00
-- url     : https://prove2.me/submissions/668def30-8e5f-4cdd-9366-b7fb24bf1c35

import Mathlib
import Definitions.Def_OAIQ039C067

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
lemma amplifiedStage_in_relative_oai (R : VonNeumannAlgebra H)
    (hE : ∀ n a,((E n).hom a:H →L[ℂ] H)∈R) (n : ℕ)
    (a : Matrix (amplifiedStage ι i₀ M (E n)).I (amplifiedStage ι i₀ M (E n)).I ℂ) :
    ((amplifiedStage ι i₀ M (E n)).hom a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)∈matrixVonNeumann ι i₀ R := by
  let S : StarSubalgebra ℂ (matrixVonNeumann ι i₀ M) :=
    (matrixVonNeumann ι i₀ R).toStarSubalgebra.comap (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
  apply MatrixTensor.range_le (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp (E n).hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x ((E n).hom y)) S _ _ ⟨a,rfl⟩
  · rintro b ⟨x,rfl⟩
    change (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)∈matrixVonNeumann ι i₀ R
    rw [scalarMatrixHom_coe]
    apply (matrixVonNeumann ι i₀ R).sum_mem
    intro i _
    apply (matrixVonNeumann ι i₀ R).sum_mem
    intro j _
    exact (matrixVonNeumann ι i₀ R).smul_mem (matrixUnit_mem ι i₀ R i j) _
  · rintro b ⟨x,rfl⟩
    exact diagonal_mem_matrixVonNeumann ι i₀ R (hE n x)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.amplifiedStage_in_relative_oai := @OAI.Kadison.OperatorAmplification.amplifiedStage_in_relative_oai
