-- Prove2me | solution 1 for IntMul.Kappa.kappaBound_of_polylog_slack
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:27:34.889569+00:00
-- url     : https://prove2.me/submissions/f562293d-746d-4979-ac8a-b23c00589fdc

import Definitions.Def_IntMul_MultitapeModel

open IntMul

theorem logpow_le (A : ℕ) (e : ℝ) (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x + 1) ^ A ≤ K * x ^ e := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · refine ⟨1, zero_le_one, fun x hx => ?_⟩
    subst hA; simp only [pow_zero, one_mul]; exact Real.one_le_rpow hx he.le
  · set ε := e / A with hε
    have hε0 : 0 < ε := div_pos he (by exact_mod_cast hA)
    refine ⟨(1 / ε + 1) ^ A, by positivity, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have hl := Real.log_le_rpow_div hx0 hε0
    have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε0.le
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : Real.log x + 1 ≤ (1 / ε + 1) * x ^ ε := by
      have : x ^ ε / ε = 1 / ε * x ^ ε := by ring
      nlinarith
    calc (Real.log x + 1) ^ A ≤ ((1 / ε + 1) * x ^ ε) ^ A := by gcongr
      _ = (1 / ε + 1) ^ A * (x ^ ε) ^ A := by rw [mul_pow]
      _ = (1 / ε + 1) ^ A * x ^ e := by
        rw [← Real.rpow_natCast (x ^ ε), ← Real.rpow_mul hx0, hε, div_mul_cancel₀ _ (by exact_mod_cast hA.ne')]

theorem multipliesAt_mono {M : MultitapeTM} {n : ℕ} {T T' : ℝ} (h : MultipliesAt M n T)
    (hT : T ≤ T') : MultipliesAt M n T' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hT, hh⟩

theorem solution (κ g C : ℝ) (A : ℕ) (hg : κ < g) (M : MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, MultipliesAt M n T) (n₀ : ℕ)
    (hT : ∀ n : ℕ, n₀ ≤ n →
      MultipliesAt M n (C * n * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A)) :
    KappaBound κ := by
  obtain ⟨K, hK0, hK⟩ := logpow_le A (g - κ) (by linarith)
  refine ⟨M, hcorr, |C| * K + 1, by positivity, n₀, fun n hn _ => ?_⟩
  apply multipliesAt_mono (hT n hn)
  have hL : (1 : ℝ) ≤ (lg n : ℝ) := by exact_mod_cast (le_max_right _ _ : 1 ≤ lg n)
  have hL0 : (0 : ℝ) < (lg n : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (lg n) + 1 := by have := Real.log_nonneg hL; linarith
  have hp := hK _ hL
  have hsplit : (lg n : ℝ) ^ (1 - g) * (lg n : ℝ) ^ (g - κ) = (lg n : ℝ) ^ (1 - κ) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hX : 0 ≤ (n : ℝ) * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A := by positivity
  calc C * n * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A
      = C * ((n : ℝ) * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A) := by ring
    _ ≤ |C| * ((n : ℝ) * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hX
    _ ≤ |C| * ((n : ℝ) * (lg n : ℝ) ^ (1 - g) * (K * (lg n : ℝ) ^ (g - κ))) := by gcongr
    _ = |C| * K * ((n : ℝ) * (lg n : ℝ) ^ (1 - κ)) := by rw [← hsplit]; ring
    _ ≤ (|C| * K + 1) * ((n : ℝ) * (lg n : ℝ) ^ (1 - κ)) := by
        have : 0 ≤ (n : ℝ) * (lg n : ℝ) ^ (1 - κ) := by positivity
        nlinarith
