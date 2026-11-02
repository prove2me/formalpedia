-- Prove2me | solution 1 for NoSignalPA.main_result
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:52:49.463622+00:00
-- url     : https://prove2.me/submissions/606f21eb-a329-44ee-a321-10f87d76ccd8

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Theorems.Thm_NoSignalPA_secure_of_long_key
import Theorems.Thm_NoSignalPA_secure_of_entrywise
import Theorems.Thm_NoSignalPA_lemma_2

namespace NoSignalPAMainAux

/-- Monotonicity of the uniform probability. -/
lemma uniformProbability_mono {α : Type} [Fintype α] (P Q : α → Prop) (h : ∀ ω, P ω → Q ω) :
    OAI.ThorpCompatibility.uniformProbability P ≤ OAI.ThorpCompatibility.uniformProbability Q := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

/-- The uniform probability of an impossible event is `0`. -/
lemma uniformProbability_false {α : Type} [Fintype α] (P : α → Prop) (h : ∀ ω, ¬ P ω) :
    OAI.ThorpCompatibility.uniformProbability P = 0 := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  have : Finset.univ.filter P = ∅ := Finset.filter_eq_empty_iff.mpr fun ω _ => h ω
  simp [this]

end NoSignalPAMainAux

open NoSignalPAMainAux in
theorem solution.{u} (Nr Ns : ℕ) :
    OAI.ThorpCompatibility.uniformProbability
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ¬ NoSignalPA.IsSecure.{u} h)
      < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := by
  by_cases hlong : (Nr : ℝ) + 2 ≤ Ns + Real.sqrt Nr
  · -- long keys: every hash function is secure
    rw [uniformProbability_false _ fun h hns => hns (NoSignalPA.secure_of_long_key hlong h)]
    positivity
  · -- otherwise Lemma 2 applies, and (6) implies security by (7)
    have hN : (Ns : ℝ) + Real.sqrt Nr ≤ Nr + 2 := by linarith
    calc OAI.ThorpCompatibility.uniformProbability
          (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ¬ NoSignalPA.IsSecure.{u} h)
        ≤ OAI.ThorpCompatibility.uniformProbability
          (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ¬ NoSignalPA.SatisfiesEq6 h) :=
          uniformProbability_mono _ _ fun h hns h6 => hns (NoSignalPA.secure_of_entrywise h h6)
      _ < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := NoSignalPA.lemma_2 hN
