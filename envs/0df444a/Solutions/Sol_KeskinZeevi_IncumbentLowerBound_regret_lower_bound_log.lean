-- Prove2me | solution 1 for KeskinZeevi.IncumbentLowerBound.regret_lower_bound_log
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:57:05.585394+00:00
-- url     : https://prove2.me/submissions/512749f5-0c16-4438-aa99-5aefc9118ff1

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
import Theorems.Thm_KeskinZeevi_IncumbentLowerBound_regret_lower_bound_harmonic
open RobustBooking.Shared
open MeasureTheory
open KeskinZeevi.IncumbentLowerBound

lemma kz_log_le_harm (T : ℕ) (hT : 1 ≤ T) :
    Real.log T ≤ ∑ t ∈ Finset.Ico 1 T, 1 / (t : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have h := log_add_one_le_harmonic n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ t ∈ Finset.Ico 1 (n + 1), 1 / (t : ℝ) := by
    rw [harmonic, Finset.sum_Ico_eq_sum_range]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div, add_comm]
  push_cast at h
  rw [← e]; exact_mod_cast h

theorem solution (M : Model) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ), 3 ≤ T →
        c * Real.log T ≤ worstRegret M P ε π T := by
  obtain ⟨K₁, hK₁, K₂, hK₂, h⟩ := regret_lower_bound_harmonic M
  refine ⟨K₁ / (1 + K₂), by positivity, ?_⟩
  intro Ω _ P _ ε hε π T hT
  obtain ⟨h1, h2⟩ := h P ε hε π T
  have hl := kz_log_le_harm T (by omega)
  calc K₁ / (1 + K₂) * Real.log T ≤ K₁ / (1 + K₂) * ∑ t ∈ Finset.Ico 1 T, 1 / (t : ℝ) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ _ := h1.trans h2
