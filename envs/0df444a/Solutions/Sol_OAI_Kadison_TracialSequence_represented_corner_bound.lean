-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.represented_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:15:36.652618+00:00
-- url     : https://prove2.me/submissions/67a01da4-14bf-451f-af0c-1c5704bf6de0

import Mathlib
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_TracialSequence_small_corner_bound

section
-- module Solutions.OAIQ039_CM.Commutator_TracialRepresentedCorner
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

open Filter

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))

variable (D : VonNeumannAlgebra (boundedSubspace τ ω))

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
  (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.range ((leftRestricted τ ω).comp (mapSequence j)))

include hτ hω hM hDQ in
lemma represented_corner_bound_oai (T : τ.GNS →L[ℂ] τ.GNS)
    {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : β<b)
    (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖) :
    VectorGNS.RepresentedCornerBound M (sequenceVacuum τ ω) D (compressed τ ω T) c (β:ℂ) := by
  intro q hq hqt a ha
  have ht : (sequenceTrace τ ω (q:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)).re<b := by
    change (VectorGNS.subalgebraTrace D (sequenceVacuum τ ω) q).re<b
    rw [hqt,Complex.ofReal_re]
    exact hβ
  exact small_corner_bound τ ω hτ Q j hω T hb hc hT hq (hDQ q) ht (hM a) ha

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.represented_corner_bound_oai := @OAI.Kadison.TracialSequence.represented_corner_bound_oai
