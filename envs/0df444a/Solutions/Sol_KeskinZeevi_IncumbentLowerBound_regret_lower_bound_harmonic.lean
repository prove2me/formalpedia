-- Prove2me | solution 1 for KeskinZeevi.IncumbentLowerBound.regret_lower_bound_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:57:06.453354+00:00
-- url     : https://prove2.me/submissions/50bca29c-1e78-41b4-a59e-2bd151d01d85

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
import Theorems.Thm_KeskinZeevi_IncumbentLowerBound_regret_eq_neg_beta_sum_sqErr
open RobustBooking.Shared
open MeasureTheory
open KeskinZeevi.IncumbentLowerBound

theorem solution (M : Model) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        K₁ / (1 + K₂) * ∑ t ∈ Finset.Ico 1 T, 1 / (t : ℝ)
            ≤ K₁ * ∑ t ∈ Finset.Ico 1 T, 1 / (K₂ + (t : ℝ)) ∧
          K₁ * ∑ t ∈ Finset.Ico 1 T, 1 / (K₂ + (t : ℝ)) ≤ worstRegret M P ε π T := by
  obtain ⟨c₀, hc₀, c₁, hc₁, h⟩ := regret_eq_neg_beta_sum_sqErr M
  have hul : 0 < (M.u - M.l) ^ 2 := by have := M.l_lt_u; positivity
  have hb : 0 < |M.bMax| := abs_pos.mpr M.bMax_neg.ne
  refine ⟨|M.bMax| * c₀ / (M.u - M.l) ^ 2, by positivity, c₁ / (M.u - M.l) ^ 2, by positivity, ?_⟩
  intro Ω _ P _ ε hε π T
  obtain ⟨-, h2⟩ := h P ε hε π T
  set K₁ := |M.bMax| * c₀ / (M.u - M.l) ^ 2
  set K₂ := c₁ / (M.u - M.l) ^ 2
  have hK₂ : 0 < K₂ := by positivity
  have hK₁ : 0 < K₁ := by positivity
  constructor
  · rw [mul_comm, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := by
      have := (Finset.mem_Ico.mp ht).1; exact_mod_cast this
    rw [div_mul_div_comm, one_mul, mul_one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hK₁.le
    nlinarith
  · refine le_trans (le_of_eq ?_) h2
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [K₁, K₂]
    have hne : (M.u - M.l) ^ 2 ≠ 0 := hul.ne'
    have hne1 : M.u - M.l ≠ 0 := sub_ne_zero.mpr M.l_lt_u.ne'
    have hpos : 0 < c₁ + (M.u - M.l) ^ 2 * (t : ℝ) := by positivity
    rw [show c₁ / (M.u - M.l) ^ 2 + (t : ℝ) = (c₁ + (M.u - M.l) ^ 2 * t) / (M.u - M.l) ^ 2 by
      field_simp]
    field_simp
