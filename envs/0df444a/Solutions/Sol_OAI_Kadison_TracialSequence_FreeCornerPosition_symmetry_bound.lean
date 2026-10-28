-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:33.605338+00:00
-- url     : https://prove2.me/submissions/8f646f46-31cb-4fa9-b5d4-3c76a287d39d

import Mathlib
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_TracialSequence_generated_free_small_corners_bound

section
-- module Solutions.OAIQ039_CM.Commutator_TracialFreePositionCriterion
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

variable {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

theorem FreeCornerPosition.symmetry_bound_oai (F : FreeCornerPosition τ ω Q j)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop) (hone : τ 1=1)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β ≤ 1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re ≤ b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖ ≤ 1040*c := by
  change FreeCornerPositionData (sequenceVacuum τ ω) (constantAction τ ω)
    (Set.range ((leftRestricted τ ω).comp (mapSequence j))) at F
  apply generated_free_small_corners_bound τ ω hτ hω hone F.algebra
    (fun n => Fin (F.size n+1)) F.stage F.inclusion F.compatible
    _ F.generated F.free Q j F.in_range F.diffuse T hTQ hb hc hβ hβ1 hβb hTC s hs0 hs2
  intro n q
  simpa only [Fintype.card_fin] using F.unbounded n q

end Kadison.TracialSequence

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound_oai := @OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound_oai
