-- Prove2me | solution 1 for OAI.KadisonSimilarity.baseWordInclusion_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:23:39.38158+00:00
-- url     : https://prove2.me/submissions/57becbd0-a5ab-4b22-b25e-018b779dc750

import Mathlib
import Definitions.Def_OAIQ075A016
import Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_intertwines

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordBaseCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
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

/-- Compressing to the base-word inclusion recovers precisely the transported
canonical degree-zero operator. -/
theorem baseWordInclusion_compression_oai (Y : H →L[ℂ] H)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.adjoint.comp
      (Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap) =
        zeroMultiplicityOperator ΩA T := by
  rw [baseWordInclusion_intertwines ΩA U ΩD hΩD Y T hY,
    ← ContinuousLinearMap.comp_assoc, LinearIsometry.adjoint_comp_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

end KadisonSimilarity

end

end OAI
end

theorem solution.{u, u_1, u_2} : type_of% @OAI.KadisonSimilarity.baseWordInclusion_compression_oai.{u, u_1, u_2} := @OAI.KadisonSimilarity.baseWordInclusion_compression_oai.{u, u_1, u_2}
