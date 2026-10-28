-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.constant_range_bicommutant_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:51:24.695435+00:00
-- url     : https://prove2.me/submissions/5836f60c-6c3e-47a0-91a9-20c595be663f

import Mathlib
import Definitions.Def_OAIQ039C064
import Theorems.Thm_OAI_Kadison_TracialSequence_constant_bicommutant_contraction

section
-- module Solutions.OAIQ039_CM.Commutator_ConstantSequenceRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

section Abstract

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

lemma constant_range_bicommutant_of_closed_oai
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hclosed : IsClosed {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x}) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=
      Set.range ((leftRestricted τ ω).comp constantSequence) := by
  exact BicommutantRange.operatorHom_range (H := boundedSubspace τ ω)
    ((leftRestricted τ ω).comp constantSequence) fun T hT hsT hnT =>
      (constant_bicommutant_contraction τ ω hτ hclosed hT hsT hnT).imp fun _ ha => ha.2

end Abstract

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.constant_range_bicommutant_of_closed_oai := @OAI.Kadison.TracialSequence.constant_range_bicommutant_of_closed_oai
