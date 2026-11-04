-- Prove2me | solution 1 for OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:23:40.668923+00:00
-- url     : https://prove2.me/submissions/c4d0f527-a6ae-4694-8d26-9bd908bbdb95

import Mathlib
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordBaseCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the degree-zero multiplicity operator with the actual compression
to the base algebra's tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

section TracialBase
variable {P : Type*} [CStarAlgebra P]
  (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) E F) H)

/-- Equality on algebra vectors identifies the abstract degree-zero inclusion
with the actual closed base subspace. The extension follows from density. -/
theorem baseWordInclusion_eq_baseInclusion_oai
    (hword : ∀ a : A,
      baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P)) :
    baseWordInclusion (G.baseVector A 1) U ΩD hΩD = G.baseInclusion A := by
  ext b
  exact (G.baseVector_dense A).induction_on b
    (isClosed_eq (by fun_prop) (by fun_prop)) hword

end TracialBase
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, u_2, u_3} : type_of% @OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion_oai.{u, u_2, u_3} := @OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion_oai.{u, u_2, u_3}
