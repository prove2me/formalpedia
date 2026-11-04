-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.baseMatrixWordAction_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:30:30.598337+00:00
-- url     : https://prove2.me/submissions/5e18c3a9-8f08-4bb6-9ad9-93e66353b0cf

import Mathlib
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialAutomorphismWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unitary word formula is derived from the algebraic product
formula and the actual implementation of a trace-preserving automorphism. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

theorem centeredMatrixConjugation_letter (c : D) (hc : G.trace (c : P) = 0) :
    centeredUnitaryConjugation (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
      (G.baseGeometry D).left_vector (G.baseGeometry D).tracial
      (G.baseGeometry D).dense_vector u (G.baseSymmetryLetter D c hc) =
    G.baseSymmetryLetter D (matrixConjugateLetter D ι u c)
      ((G.trace_matrixConjugateLetter D ι u c).trans hc) := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_apply_vector (G.baseGeometry D).trace
    (G.baseGeometry D).vector (G.baseGeometry D).left ι
    (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
    (G.baseGeometry D).tracial (G.baseGeometry D).dense_vector u c

/-- The completed endpoint action sends every bounded tensor word to the
word whose other-factor letters have been conjugated. -/
theorem baseMatrixWordAction_endpoint_oai (n : ℕ) (d : D) (c : Fin n → D)
    (hc : ∀ i, G.trace (c i : P) = 0) :
    G.baseMatrixWordAction D ι u n (tracialEndpointWord G D n d c hc) =
      tracialEndpointWord G D n (matrixConjugateLetter D ι u d)
        (fun i => matrixConjugateLetter D ι u (c i))
        (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i)) := by
  simp only [baseMatrixWordAction, tracialMatrixWordAction, tracialEndpointWord]
  erw [endpointTensorIsometry_apply]
  apply congrArg₂ (fun d (x : Fin n → centeredSubspace (G.baseVector D 1)) =>
    endpointWord d x)
  · exact tracialUnitaryConjugation_apply_vector (G.baseGeometry D).trace
      (G.baseGeometry D).vector (G.baseGeometry D).left ι
      (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
      (G.baseGeometry D).tracial (G.baseGeometry D).dense_vector u d
  · funext i
    exact G.centeredMatrixConjugation_letter D ι u (c i) (hc i)

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.baseMatrixWordAction_endpoint_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.TracialCornerGeometry.baseMatrixWordAction_endpoint_oai.{u_1, u_2, u_3}
