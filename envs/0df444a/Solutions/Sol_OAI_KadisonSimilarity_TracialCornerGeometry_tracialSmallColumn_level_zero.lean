-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:28:11.186269+00:00
-- url     : https://prove2.me/submissions/c4228074-994a-4a67-81b0-aaca030ad210

import Mathlib
import Definitions.Def_OAIQ075A023

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem baseInclusion_adjoint :
    (G.baseInclusion A).toContinuousLinearMap.adjoint =
      (G.baseSpace A).toSubmodule.orthogonalProjectionOnto :=
  (G.baseSpace A).toSubmodule.adjoint_subtypeL

/-- Preservation of the base subspace gives the actual compressed
intertwining identity. -/
theorem baseOperator_intertwines (Y : H →L[ℂ] H)
    (hY : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A) :
    Y.comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseOperator A Y) := by
  ext x
  change Y (x : H) = (G.baseInclusion A)
    ((G.baseInclusion A).toContinuousLinearMap.adjoint (Y (x : H)))
  rw [G.baseInclusion_adjoint]
  change Y (x : H) = (G.baseSpace A).toSubmodule.starProjection (Y (x : H))
  exact (Submodule.starProjection_eq_self_iff.mpr (hY x x.property)).symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small vectors in propagation are actual left compressions of the
completed base space. Scalar freeness gives their exact norm, first on
algebra vectors and then throughout the completion by density. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Commutation with the projection transfers the base action to the small
column, giving the level-zero identity required by propagation. -/
theorem tracialSmallColumn_intertwines (q : P) (Y : H →L[ℂ] H)
    (B₀ : G.baseSpace A →L[ℂ] G.baseSpace A)
    (hbase : Y.comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp B₀)
    (hcomm : Y.comp (G.left q) = (G.left q).comp Y) :
    Y.comp (G.tracialSmallColumn A q) = (G.tracialSmallColumn A q).comp B₀ := by
  change Y.comp ((G.left q).comp (G.baseInclusion A).toContinuousLinearMap) =
    ((G.left q).comp (G.baseInclusion A).toContinuousLinearMap).comp B₀
  rw [← ContinuousLinearMap.comp_assoc, hcomm, ContinuousLinearMap.comp_assoc,
    hbase, ← ContinuousLinearMap.comp_assoc]

/-- Invariance of the actual base subspace identifies the level-zero
operator with the actual compression of the ambient operator. -/
theorem tracialSmallColumn_level_zero_oai (q : P) (Y : H →L[ℂ] H)
    (hbase : ∀ v ∈ G.baseSpace A, Y v ∈ G.baseSpace A)
    (hcomm : Y.comp (G.left q) = (G.left q).comp Y) (v : G.baseSpace A) :
    Y (G.tracialSmallColumn A q v) =
      G.tracialSmallColumn A q (G.baseOperator A Y v) := by
  exact congrArg (fun T : G.baseSpace A →L[ℂ] H => T v)
    (G.tracialSmallColumn_intertwines A q Y (G.baseOperator A Y)
      (G.baseOperator_intertwines A Y hbase) hcomm)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_level_zero_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_level_zero_oai.{u_1, u_2}
