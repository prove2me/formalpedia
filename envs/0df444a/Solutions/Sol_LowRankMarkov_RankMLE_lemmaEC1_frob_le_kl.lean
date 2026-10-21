-- Prove2me | solution 1 for LowRankMarkov.RankMLE.lemmaEC1_frob_le_kl
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:30:22.733736+00:00
-- url     : https://prove2.me/submissions/e461ff69-5c4a-4a00-8470-fe89d5f47094

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting
import Theorems.Thm_LowRankMarkov_RankMLE_lemmaEC1_kl_ge_sq

open LowRankMarkov.RankMLE

theorem solution {p r : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P Q : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (hQ : ConcentrationClass α β P Q) :
    ∑ i, ∑ j, (P i j - Q i j) ^ 2 ≤ 2 * β ^ 2 / (α * piMin π * p) * klDiv π P Q := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0; simp [klDiv]
  have hp : 0 < (p : ℝ) := by exact_mod_cast hp0
  haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := π)
  have hmin_pos : 0 < piMin π := by unfold piMin; rw [← hi₀]; exact hπ_pos i₀
  have hmin_le : ∀ i, piMin π ≤ π i := fun i => ciInf_le (Finite.bddBelow_range π) i
  set c : ℝ := (p : ℝ) * α / (2 * β ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have hrow : ∀ i, c * ∑ j, (P i j - Q i j) ^ 2 ≤ klVec (P i) (Q i) := fun i =>
    lemmaEC1_kl_ge_sq α β hα hβ (P i) (Q i) (hP.2 i) (hQ.2.1 i) (hA1.2 i) (hQ.2.2 i)
  have hkl : klDiv π P Q = ∑ i, π i * klVec (P i) (Q i) := by
    unfold klDiv klVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hconst : 2 * β ^ 2 / (α * piMin π * p) = 1 / (c * piMin π) := by
    rw [hc]; field_simp
  rw [hconst, hkl, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := hrow i
  have hS : 0 ≤ ∑ j, (P i j - Q i j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hK : 0 ≤ klVec (P i) (Q i) := le_trans (mul_nonneg hc0.le hS) h1
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  calc (∑ j, (P i j - Q i j) ^ 2) * (c * piMin π)
      = (c * ∑ j, (P i j - Q i j) ^ 2) * piMin π := by ring
    _ ≤ klVec (P i) (Q i) * piMin π := mul_le_mul_of_nonneg_right h1 hmin_pos.le
    _ ≤ klVec (P i) (Q i) * π i := mul_le_mul_of_nonneg_left (hmin_le i) hK
    _ = π i * klVec (P i) (Q i) := by ring
