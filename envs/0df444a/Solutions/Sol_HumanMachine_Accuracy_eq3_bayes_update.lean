-- Prove2me | solution 1 for HumanMachine.Accuracy.eq3_bayes_update
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:33:35.114969+00:00
-- url     : https://prove2.me/submissions/cc57e44a-363b-497a-9caf-4bfc7fd53768

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

set_option autoImplicit false
open HumanMachine.Accuracy

theorem solution (π : Bool → Bool → ℝ) (hπ : IsPrior π) :
    posterior π false = 0 ∧
      posterior π true = priorGood π / (priorGood π + π true false) ∧
      priorGood π < posterior π true := by
  obtain ⟨hpos, hsum⟩ := hπ
  have h1 : posterior π false = 0 := by
    simp [posterior, jointGood, isGood, Fintype.sum_bool]
  have hP : priorGood π = π true true := by
    simp [priorGood, isGood, Fintype.sum_bool]
  have h2 : posterior π true = priorGood π / (priorGood π + π true false) := by
    simp [posterior, jointGood, probOut, isGood, Fintype.sum_bool, hP]
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  have ha : 0 < priorGood π := by rw [hP]; exact hpos _ _
  have hb : 0 < π true false := hpos _ _
  rw [lt_div_iff₀ (by linarith)]
  have h3 := hpos false true
  have h4 := hpos false false
  have h5 : priorGood π + π true false < 1 := by rw [hP]; linarith
  nlinarith
