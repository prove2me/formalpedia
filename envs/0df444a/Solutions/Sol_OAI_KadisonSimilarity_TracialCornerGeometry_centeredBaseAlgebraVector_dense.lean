-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.centeredBaseAlgebraVector_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:26:20.202675+00:00
-- url     : https://prove2.me/submissions/c6be9a8b-d439-4c90-bcc8-7d13cd714b39

import Mathlib
import Definitions.Def_OAIQ075A024

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CenteredBaseDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-zero algebra elements are dense in the actual centered base space.
This extends elementary reduced-word identities to completed tensor letters. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

theorem centeredBaseAlgebraVector_dense_oai (hτ : G.trace 1 = 1) :
    DenseRange (G.centeredBaseAlgebraVector A) := by
  have hd := denseRange_tracialCenter (G.baseVector A) (G.baseVector_dense A)
  apply hd.mono
  rintro _ ⟨a, rfl⟩
  let a₀ : A := a - G.trace (a : P) • 1
  have ha₀ : G.trace (a₀ : P) = 0 := by
    change (G.baseGeometry A).trace (a - (G.baseGeometry A).trace a • 1) = 0
    exact trace_sub_trace _ (G.baseGeometry_trace_one A hτ) a
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  apply Subtype.ext
  change G.baseVector A a₀ = (tracialCenter (G.baseVector A) a : G.baseSpace A)
  rw [coe_tracialCenter (G.baseGeometry A).trace (G.baseVector A)
    (G.baseVector_inner A) (G.baseGeometry_trace_one A hτ)]
  change G.baseVector A (a - G.trace (a : P) • 1) = _
  rw [map_sub, map_smul]
  rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.centeredBaseAlgebraVector_dense_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.centeredBaseAlgebraVector_dense_oai.{u_1, u_2}
