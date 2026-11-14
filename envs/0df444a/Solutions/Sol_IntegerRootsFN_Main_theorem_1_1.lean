-- Prove2me | solution 1 for IntegerRootsFN.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fffmath
-- created : 2026-11-13T07:35:20.330201+00:00
-- url     : https://prove2.me/submissions/5eb3b059-7123-4e1b-8be9-7d7b13dd9082
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic.Positivity
import Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_machine
import Theorems.Thm_IntegerRootsFN_Main_approximation_candidate_machine
import Theorems.Thm_IntegerRootsFN_Main_candidate_filtering_machine
import Theorems.Thm_IntegerRootsFN_Main_proposition_A_3
import Theorems.Thm_IntegerRootsFN_Main_proposition_3_4
import Theorems.Thm_IntegerRootsFN_Main_lemma_2_2
import Theorems.Thm_IntegerRootsFN_Main_lemma_3_5

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution :
    (∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      RootRuns A f n b
        (softBound C k l n b ((n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2))) ∧
    (∃ B : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      RootRuns B f n b (softBound C k l n b ((n : ℝ) * b))) := by
  constructor
  · apply candidate_filtering_machine
      (fun n b => (n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)
    · intro n b hn hb
      exact le_add_of_nonneg_right (by positivity)
    · exact lemma_3_5
    · exact elementary_candidate_machine proposition_A_3
  · apply candidate_filtering_machine (fun n b => (n : ℝ) * b)
    · intro n b hn hb
      exact le_rfl
    · exact lemma_3_5
    · exact approximation_candidate_machine proposition_3_4 lemma_2_2
