-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.positive_rational_finite_family_has_integer_common_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T20:21:00.927+00:00
-- url     : https://prove2.me/submissions/d9fd14d5-c431-4bdc-ae27-6583cb18c44b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_positive_rational_q_finite_family_has_integer_common_multiple

theorem solution
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hwr : ∀ i, ∃ q : ℚ, w i = (q : ℝ)) :
    ∃ S : ℝ, 0 < S ∧ ∃ e : Fin n → ℕ, (∀ i, 0 < e i) ∧
      ∀ i, S = (e i : ℝ) * w i := by
  classical
  choose q hq using hwr
  have hqpos : ∀ i, 0 < q i := by
    intro i
    have hi : (0 : ℝ) < (q i : ℝ) := by
      rw [← hq i]
      exact hw i
    exact_mod_cast hi
  obtain ⟨s, hspos, e, hepos, hs⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.positive_rational_q_finite_family_has_integer_common_multiple q hqpos
  refine ⟨(s : ℝ), by exact_mod_cast hspos, e, hepos, ?_⟩
  intro i
  rw [hq i]
  exact_mod_cast hs i