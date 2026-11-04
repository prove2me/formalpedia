-- Prove2me | solution 1 for OAI.SignedSweeps.signed_occurrence_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:52:50.051824+00:00
-- url     : https://prove2.me/submissions/b85593f6-d09c-438d-920f-594a94067324

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2
import Theorems.Thm_OAI_SignedSweeps_signed_occurrence_moment_bound_fixed

section
-- module OAI.Probability.SignedSweeps.UniformMoment
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

theorem signed_occurrence_moment_bound_oai :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < η / 256 ∧
          ∀ κ : ℝ, 0 < κ → κ < κ₀ →
            ∃ r : ℕ, 1 ≤ r ∧
              ∀ d : ℕ, 1 ≤ d →
                ∀ lam : Partition (2 ^ d),
                  ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
                    (α : Partition u) (β : Partition v) (γ : Partition l),
                    SignedOccurrence h α β γ lam →
                      logMoment (weightedMoment lam r) ≤
                        ((coefficient η d * signedEntropy α β +
                            remainderBudget κ d l : ℝ) : EReal) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro η hη hη1
  refine ⟨η/512, by positivity, by linarith, ?_⟩
  intro κ hκ hκsmall
  exact signed_occurrence_moment_bound_fixed hη hη1 hκ (by linarith)

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_occurrence_moment_bound_oai := @OAI.SignedSweeps.signed_occurrence_moment_bound_oai
