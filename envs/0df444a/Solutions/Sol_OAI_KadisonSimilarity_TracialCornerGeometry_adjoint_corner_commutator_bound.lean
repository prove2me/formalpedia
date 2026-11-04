-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:22:06.713081+00:00
-- url     : https://prove2.me/submissions/18b09575-ce61-4bac-b03f-0bc98768530e

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AdjointCommutators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjoint version of a scalar corner estimate, used in propagation. -/

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Taking adjoints exchanges the two commutator factors and changes the sign. -/
theorem commutator_adjoint_left (Y X : H →L[ℂ] H) :
    commutator (star Y) X = -star (commutator Y (star X)) := by
  simp only [commutator, star_sub, star_mul, star_star, neg_sub]

theorem norm_commutator_adjoint_left (Y X : H →L[ℂ] H) :
    ‖commutator (star Y) X‖ = ‖commutator Y (star X)‖ := by
  rw [commutator_adjoint_left, norm_neg]
  exact ContinuousLinearMap.adjoint.norm_map _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialAdjointBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
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

theorem adjoint_corner_commutator_bound_oai (e : P) (he : IsStarProjection e)
    (Y : H →L[ℂ] H) {ε : ℝ}
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (x : CStarCorner e he) :
    ‖commutator Y.adjoint (G.left (x : P))‖ ≤ ε * ‖x‖ := by
  have hx : star (G.left (x : P)) = G.left (star (x : P)) := (map_star G.left _).symm
  change ‖commutator (star Y) (G.left (x : P))‖ ≤ _
  rw [norm_commutator_adjoint_left, hx]
  have h := hY (star x)
  simpa only [StarMemClass.coe_star, norm_star] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound_oai.{u_1, u_2}
