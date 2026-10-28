-- Prove2me | solution 1 for OAI.Kadison.matrixOperator_subtype_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:33:50.119484+00:00
-- url     : https://prove2.me/submissions/056697fe-072d-4ff6-8cab-c0cb6a645b17

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C022
import Theorems.Thm_OAI_Kadison_CyclicSpatial_matrixRepresentation_norm_eq

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma matrixRepresentation_norm_le (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix ι ι A) :
    ‖matrixRepresentation σ X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation σ) X

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentationMatrixNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixOperator_representation (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) :
    matrixOperator h (fun i j => φ (X i j))=
      CyclicColumns.matrixRepresentation φ (CStarMatrix.ofMatrix X) := rfl

lemma matrixOperator_representation_norm_le (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) :
    ‖matrixOperator h (fun i j => ψ (X i j))‖≤‖matrixOperator h (fun i j => φ (X i j))‖ := by
  rw [matrixOperator_representation,matrixOperator_representation,
    CyclicSpatial.matrixRepresentation_norm_eq φ hφ]
  exact CyclicColumns.matrixRepresentation_norm_le ψ _

lemma matrixOperator_subtype_norm_le_oai (M : VonNeumannAlgebra H)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖matrixOperator h (fun i j => ψ ⟨X i j,hX i j⟩)‖≤‖matrixOperator h X‖ :=
  matrixOperator_representation_norm_le (A:=M) (H:=H) (G:=G)
    M.toStarSubalgebra.subtype Subtype.val_injective ψ h (fun i j => ⟨X i j,hX i j⟩)

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.matrixOperator_subtype_norm_le_oai.{u_1, u_2} := @OAI.Kadison.matrixOperator_subtype_norm_le_oai.{u_1, u_2}
