-- Prove2me | solution 1 for LassoDantzig.Dantzig.eq_B26
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:13:16.323145+00:00
-- url     : https://prove2.me/submissions/7fb6bd84-25c7-4708-b5b4-49b6e0d177d6

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

theorem aux_eqB26_key {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s : ℕ) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ) :
    κ ^ 2 * (l2On δ J0) ^ 2 ≤ (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 := by
  have hS0 : 0 ≤ ∑ i, X.mulVec δ i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ha0 : 0 ≤ l2On δ J0 := Real.sqrt_nonneg _
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  by_cases hδ : δ = 0
  · have : l2On δ J0 = 0 := by simp [l2On, hδ]
    rw [this]
    have : 0 ≤ (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 := by positivity
    simpa using this
  · have h := hRE J0 hJ0 δ hδ hcone
    unfold euclNorm at h
    have h1 : 0 ≤ κ * Real.sqrt n * l2On δ J0 := by positivity
    have h2 := pow_le_pow_left₀ h1 h 2
    rw [Real.sq_sqrt hS0, mul_pow, mul_pow, Real.sq_sqrt hnpos.le] at h2
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hnpos]
    nlinarith

end LassoDantzig.Dantzig

open LassoDantzig.Dantzig

theorem solution {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s : ℕ) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
    l2On δ J0 ≤ 4 * r * Real.sqrt s / κ ^ 2 := by
  have key := aux_eqB26_key hn X s κ hκ hRE J0 hJ0 δ hcone
  have ha0 : 0 ≤ l2On δ J0 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ 4 * r * Real.sqrt s := by positivity
  have hk2 : 0 < κ ^ 2 := by positivity
  have hss : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (by positivity)
  have hmain : l2On δ J0 ≤ 4 * r * Real.sqrt s / κ ^ 2 := by
    rw [le_div_iff₀ hk2]
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; simpa using hc0
    · have h3 : (l2On δ J0 * κ ^ 2) * l2On δ J0 ≤ (4 * r * Real.sqrt s) * l2On δ J0 := by
        nlinarith
      exact le_of_mul_le_mul_right h3 h
  refine ⟨?_, hmain⟩
  calc (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0 := hB25
    _ ≤ 4 * r * Real.sqrt s * (4 * r * Real.sqrt s / κ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain hc0
    _ = 16 * r ^ 2 * s / κ ^ 2 := by
        rw [mul_div_assoc']
        congr 1
        nlinarith [hss]
