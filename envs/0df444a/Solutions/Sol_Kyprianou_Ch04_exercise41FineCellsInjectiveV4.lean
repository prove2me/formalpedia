-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FineCellsInjectiveV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:24:55.712371+00:00
-- url     : https://prove2.me/submissions/f6ff9e52-2195-4edf-9ca6-df293414ee7c

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (S : Finset NNReal) (a : ℝ) (h : ℕ → ℝ)
    (ht : Tendsto h atTop (𝓝 0))
    (j : ℕ → NNReal → ℕ)
    (hc : ∀ n s, s ∈ S → a + (j n s : ℝ) * h n ≤ (s : ℝ) ∧
      (s : ℝ) < a + ((j n s : ℝ) + 1) * h n) :
    ∀ᶠ n in atTop, Set.InjOn (j n) (S : Set NNReal) := by
  have hev : ∀ s ∈ S, ∀ t ∈ S,
      ∀ᶠ n in atTop, s ≠ t → j n s ≠ j n t := by
    intro s hs t ht'
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun _ hn => (hn hst).elim
    have hpos : 0 < |(s : ℝ) - (t : ℝ)| := by
      apply abs_pos.mpr
      exact sub_ne_zero.mpr (fun he => hst (NNReal.coe_injective he))
    filter_upwards [ht.eventually_lt_const hpos] with n hn hne heq
    have hs' := hc n s hs
    have ht'' := hc n t ht'
    rw [← heq] at ht''
    rcases abs_cases ((s : ℝ) - (t : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hn
      linarith
    · rw [he] at hn
      linarith
  have hAll : ∀ᶠ n in atTop, ∀ s ∈ S, ∀ t ∈ S,
      s ≠ t → j n s ≠ j n t :=
    (Filter.eventually_all_finset S).2 fun s hs =>
      (Filter.eventually_all_finset S).2 fun t ht' => hev s hs t ht'
  filter_upwards [hAll] with n hn
  intro s hs t ht' he
  by_contra hne
  exact hn s hs t ht' hne he
