-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_commutes_with_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:21:43.251191+00:00
-- url     : https://prove2.me/submissions/d586a8b4-01f5-42d2-b5f3-08d31bcf3af4

import Mathlib
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialAdjointBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same corner hypotheses hold for the adjoint operator, so the
propagation argument supplies both errors in the final compression. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem adjoint_commutes_with_base_oai (D : StarSubalgebra ℂ P) (Y : H →L[ℂ] H)
    (hY : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y) (x : D) :
    Y.adjoint.comp (G.left (x : P)) = (G.left (x : P)).comp Y.adjoint := by
  have hx : (G.left (star (x : P))).adjoint = G.left (x : P) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
  have h := congrArg (fun T : H →L[ℂ] H => T.adjoint) (hY (star x))
  simpa only [ContinuousLinearMap.adjoint_comp, StarMemClass.coe_star, hx] using h.symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_commutes_with_base_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_commutes_with_base_oai.{u_1, u_2}
