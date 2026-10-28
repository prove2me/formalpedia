-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.sequenceUnitary_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:15:37.782545+00:00
-- url     : https://prove2.me/submissions/c72391ce-79ce-43a2-9c11-9a0c6cff4a86

import Mathlib
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_FinitePatching_ConjugatedWords_free_of_centered_unitary_words
import Theorems.Thm_OAI_Kadison_FinitePatching_Words_moment_limit_of_contractions
import Theorems.Thm_OAI_Kadison_TracialSequence_trace_mul
import Theorems.Thm_OAI_Kadison_TracialSequence_trace_sequence_word

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSequenceUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma sequenceUnitary_free_oai (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (hlim : ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
      ((leftRestricted τ ω).comp constantSequence) (sequenceUnitary τ ω u))
      (sequenceTrace τ ω).toLinearMap := by
  apply free_of_centered_unitary_words (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    _ _ (leftRestricted τ ω).range (sequenceTrace τ ω).toLinearMap
    τ.toLinearMap
  · exact ⟨boundedUnitary u,rfl⟩
  · intro a
    exact ⟨constantSequence a,rfl⟩
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    change sequenceTrace τ ω (leftRestricted τ ω a * leftRestricted τ ω b)=
      sequenceTrace τ ω (leftRestricted τ ω b * leftRestricted τ ω a)
    exact (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
      sequenceTrace τ ω T) (map_mul (leftRestricted τ ω) a b)).symm.trans
        ((trace_mul τ ω hτ a b).trans
          (congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
            sequenceTrace τ ω T) (map_mul (leftRestricted τ ω) b a)))
  · exact trace_constant τ ω
  · intro J x hx l hl hv
    apply trace_sequence_word τ ω hω u x signPower l
    exact moment_limit_of_contractions τ signPower (fun n => PartialUnitary.ofUnitary (u n))
      (hlim J) x hx l hl hv

end Kadison.TracialSequence

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.sequenceUnitary_free_oai := @OAI.Kadison.TracialSequence.sequenceUnitary_free_oai
