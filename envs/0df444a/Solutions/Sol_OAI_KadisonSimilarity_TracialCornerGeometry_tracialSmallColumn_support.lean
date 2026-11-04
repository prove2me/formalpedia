-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:28:35.187907+00:00
-- url     : https://prove2.me/submissions/c66cb7cb-7722-436a-9cc9-1c629fe64113

import Mathlib
import Definitions.Def_OAIQ075A023

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

/-- The small column is supported by its defining projection. -/
theorem tracialSmallColumn_support_oai (q : P) (hq : IsStarProjection q) :
    (G.left q).comp (G.tracialSmallColumn A q) = G.tracialSmallColumn A q := by
  ext v
  change (G.left q * G.left q) (v : H) = G.left q (v : H)
  rw [← map_mul, hq.isIdempotentElem.eq]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_support_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_support_oai.{u_1, u_2}
