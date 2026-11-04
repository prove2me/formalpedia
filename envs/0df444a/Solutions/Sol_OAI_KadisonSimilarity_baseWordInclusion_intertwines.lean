-- Prove2me | solution 1 for OAI.KadisonSimilarity.baseWordInclusion_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:24:25.490235+00:00
-- url     : https://prove2.me/submissions/654ba982-e906-47d1-8f4d-7c73ce9a3e5d

import Mathlib
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordBaseCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
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

omit [CompleteSpace H] in
/-- The degree-zero repeated-word identity determines the base operator. -/
theorem baseWordInclusion_intertwines_oai (Y : H →L[ℂ] H)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap =
      (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.comp
        (zeroMultiplicityOperator ΩA T) := by
  ext b
  change Y (U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
      (emptyEndpoint (F := F) ΩD))) =
    U.inclusion 0 (hilbertTensorInsert
      (zeroMultiplicityEquiv ΩA (zeroMultiplicityOperator ΩA T b))
      (emptyEndpoint (F := F) ΩD))
  rw [hY, zeroMultiplicityOperator_intertwines]

end KadisonSimilarity

end

end OAI
end

theorem solution.{u, u_1, u_2} : type_of% @OAI.KadisonSimilarity.baseWordInclusion_intertwines_oai.{u, u_1, u_2} := @OAI.KadisonSimilarity.baseWordInclusion_intertwines_oai.{u, u_1, u_2}
