-- Prove2me | solution 2 for OAI.PiExponent.main
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-11T02:27:05.190392+00:00
-- url     : https://prove2.me/submissions/12cb7def-e37d-4c8c-89f0-2950e8f320b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_floor_bracket_lower_bound
import Theorems.Thm_OAI_PiExponent_eventualLowerBound_iff_integer
import Theorems.Thm_OAI_PiExponent_pi_irrationalityExponent_eq_two_of_eventualLowerBound

open OAI.PiExponent

theorem solution :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  have hNat : PiEventualLowerBound := by
    intro ν hν
    obtain ⟨Q, hQ, hbracket⟩ :=
      OAI.PiExponent.pi_floor_bracket_lower_bound ν hν
    refine ⟨Q, hQ, ?_⟩
    intro p q hq
    have hqpos : 0 < q := by omega
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
    let n : ℤ := Int.floor ((q : ℝ) * Real.pi)
    have hnle : (n : ℝ) ≤ (q : ℝ) * Real.pi := by
      dsimp [n]
      exact Int.floor_le _
    have hlt : (q : ℝ) * Real.pi < (n : ℝ) + 1 := by
      dsimp [n]
      exact Int.lt_floor_add_one _
    have hnq : (n : ℝ) / (q : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hqR).2
      nlinarith [hnle]
    have hupper : Real.pi < ((n + 1 : ℤ) : ℝ) / (q : ℝ) := by
      apply (lt_div_iff₀ hqR).2
      push_cast
      nlinarith [hlt]
    by_cases hpn : p ≤ n
    · have hpq : (p : ℝ) / (q : ℝ) ≤ (n : ℝ) / (q : ℝ) :=
          div_le_div_of_nonneg_right (Int.cast_le.mpr hpn) (le_of_lt hqR)
      have hpi_non : 0 ≤ Real.pi - (n : ℝ) / (q : ℝ) := by linarith
      have hp_non : 0 ≤ Real.pi - (p : ℝ) / (q : ℝ) := by linarith
      rcases hbracket q hq with ⟨hlo, hhi⟩
      rw [abs_of_nonneg hpi_non] at hlo
      rw [abs_of_nonneg hp_non]
      linarith
    · have hnp' : n + 1 ≤ p := by omega
      have hpq : ((n + 1 : ℤ) : ℝ) / (q : ℝ) ≤ (p : ℝ) / (q : ℝ) :=
          div_le_div_of_nonneg_right (Int.cast_le.mpr hnp') (le_of_lt hqR)
      have hupper_non : Real.pi - ((n + 1 : ℤ) : ℝ) / (q : ℝ) ≤ 0 := by
        linarith
      have hp_non : Real.pi - (p : ℝ) / (q : ℝ) ≤ 0 := by linarith
      rcases hbracket q hq with ⟨hlo, hhi⟩
      rw [abs_of_nonpos hupper_non] at hhi
      rw [abs_of_nonpos hp_non]
      linarith
  constructor
  · exact (eventualLowerBound_iff_integer Real.pi).mp hNat
  · exact pi_irrationalityExponent_eq_two_of_eventualLowerBound hNat
