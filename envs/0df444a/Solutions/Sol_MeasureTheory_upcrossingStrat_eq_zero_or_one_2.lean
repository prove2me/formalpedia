-- Prove2me | solution 2 for MeasureTheory.upcrossingStrat_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:00:04.896722+00:00
-- url     : https://prove2.me/submissions/bdc0899a-deea-4c5a-96a8-7b1829167b35

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000

open MeasureTheory

theorem solution {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  have h1 : upcrossingStrat a b f N n ω ≤ 1 := upcrossingStrat_le_one
  have hint : ∃ m : ℕ, upcrossingStrat a b f N n ω = (m : ℝ) := by
    rw [upcrossingStrat]
    induction Finset.range N using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      obtain ⟨m, hm⟩ := ih
      by_cases hmem : n ∈ Set.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)
      · exact ⟨1 + m, by simp [Set.indicator_of_mem hmem, hm]⟩
      · exact ⟨m, by simp [Set.indicator_of_notMem hmem, hm]⟩
  obtain ⟨m, hm⟩ := hint
  rw [hm] at h1 ⊢
  have hm_le : m ≤ 1 := by exact_mod_cast h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm_le with rfl | rfl
  · left; simp
  · right; simp
