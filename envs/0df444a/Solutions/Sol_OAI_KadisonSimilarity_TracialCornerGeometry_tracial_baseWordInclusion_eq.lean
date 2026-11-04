-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.tracial_baseWordInclusion_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:28:36.8582+00:00
-- url     : https://prove2.me/submissions/0db9c512-1261-4a55-acd7-a26a4e84e350

import Mathlib
import Definitions.Def_OAIQ075A024
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracial_baseWordInclusion_vector
import Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_eq_baseInclusion

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordBase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vacuum endpoint in degree zero is the actual base Hilbert space.
Consequently the repeated-word action implies base-space invariance; this
is not an additional assumption on the symmetrized operator. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityInnerFamily
variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hU : TracialWordFormula G A D U)

include hτ hU

/-- Equality extends to the completed base space by density. -/
theorem tracial_baseWordInclusion_eq_oai :
    baseWordInclusion (G.baseVector A 1) U (G.baseVector D 1)
      (G.norm_baseVector_one D hτ) = G.baseInclusion A :=
  baseWordInclusion_eq_baseInclusion (G.baseVector D 1) (G.norm_baseVector_one D hτ)
    G A U (G.tracial_baseWordInclusion_vector A D hτ U hU)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.tracial_baseWordInclusion_eq_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.tracial_baseWordInclusion_eq_oai.{u_1, u_2}
