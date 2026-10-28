-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.constant_bicommutant_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:57.808253+00:00
-- url     : https://prove2.me/submissions/0a83cdb6-8b2f-4ae9-be5f-719d91c33114

import Mathlib
import Definitions.Def_OAIQ039C069

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

include hτ in
lemma constant_bicommutant_contraction_oai (hclosed : IsClosed {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x})
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : A, ‖a‖≤1 ∧ leftRestricted τ ω (constantSequence a)=T := by
  let φ := (leftRestricted τ ω).comp constantSequence
  have hx : T (sequenceVacuum τ ω)∈closure
      {x : boundedSubspace τ ω | ∃ a : A, ‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,ha⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit φ hT hsT hnT (fun _ => sequenceVacuum τ ω) ε hε
    refine ⟨vectorIn τ ω (constantSequence a),⟨a,hna,rfl⟩,?_⟩
    rw [dist_eq_norm,norm_sub_rev]
    change ‖vectorIn τ ω (constantSequence a)-T (sequenceVacuum τ ω)‖<ε
    rw [←leftRestricted_vacuum]
    exact ha ()
  rw [hclosed.closure_eq] at hx
  obtain ⟨a,hna,ha⟩ := hx
  refine ⟨a,hna,bicommutant_eq_of_vacuum τ ω hτ _ _ ?_ ?_ ?_⟩
  · exact Set.subset_centralizer_centralizer (Set.mem_range_self (constantSequence a))
  · intro c hc
    apply hT c
    rintro _ ⟨b,rfl⟩
    exact hc _ ⟨constantSequence b,rfl⟩
  · simpa only [leftRestricted_vacuum] using ha

end Abstract

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.constant_bicommutant_contraction_oai := @OAI.Kadison.TracialSequence.constant_bicommutant_contraction_oai
