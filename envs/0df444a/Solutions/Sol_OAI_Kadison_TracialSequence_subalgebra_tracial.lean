-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.subalgebra_tracial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:17:49.354138+00:00
-- url     : https://prove2.me/submissions/1f25c20e-97f1-403d-9d65-01c2174d1019

import Mathlib
import Definitions.Def_OAIQ039C064
import Theorems.Thm_OAI_Kadison_TracialSequence_bicommutant_trace_mul

section
-- module Solutions.OAIQ039_CM.Commutator_TracialVectorSubalgebra
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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤Filter.atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))

include hτ hω hM in
lemma subalgebra_tracial_oai (a b : M) :
    VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (a*b)=
      VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (b*a) :=
  bicommutant_trace_mul τ ω hτ hω (hM a) (hM b)

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.subalgebra_tracial_oai := @OAI.Kadison.TracialSequence.subalgebra_tracial_oai
