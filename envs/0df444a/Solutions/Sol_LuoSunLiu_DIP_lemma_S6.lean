-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_S6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:54:06.790091+00:00
-- url     : https://prove2.me/submissions/044e0763-cafb-4784-81e1-8fa554947042

import Mathlib
set_option autoImplicit false

theorem key_alg (C1 lam d ℓ L lT A : ℝ) (hlam : 0 < lam) (hd1 : 1 ≤ d) (hℓ1 : 1 ≤ ℓ)
    (hL0 : 0 ≤ L) (hLℓ : L ≤ ℓ) (hAℓ : A ≤ ℓ) (hlT : lT ≤ ℓ) :
    (1 + (2 * C1 ^ 2 * (lam * d) + 2 * (2 * lT + d * A))) * L
      ≤ (2 * C1 ^ 2 * lam + 7) * d * ℓ ^ 2 := by
  have hd0 : 0 ≤ d := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by
    calc ℓ = ℓ * 1 := by ring
      _ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_left hℓ1 hℓ0
      _ = ℓ ^ 2 := by ring
  have hℓd : ℓ ^ 2 ≤ d * ℓ ^ 2 := by
    calc ℓ ^ 2 = 1 * ℓ ^ 2 := by ring
      _ ≤ d * ℓ ^ 2 := mul_le_mul_of_nonneg_right hd1 (by positivity)
  have t1 : L ≤ d * ℓ ^ 2 := le_trans hLℓ (le_trans hℓℓ hℓd)
  have hLℓ2 : L ≤ ℓ ^ 2 := le_trans hLℓ hℓℓ
  have t2 : C1 ^ 2 * lam * d * L ≤ C1 ^ 2 * lam * d * ℓ ^ 2 :=
    mul_le_mul_of_nonneg_left hLℓ2 (by positivity)
  have t3 : lT * L ≤ d * ℓ ^ 2 := by
    have : lT * L ≤ ℓ * ℓ := mul_le_mul hlT hLℓ hL0 hℓ0
    calc lT * L ≤ ℓ * ℓ := this
      _ = ℓ ^ 2 := by ring
      _ ≤ _ := hℓd
  have t4 : A * L ≤ ℓ ^ 2 := by
    have : A * L ≤ ℓ * ℓ := mul_le_mul hAℓ hLℓ hL0 hℓ0
    calc A * L ≤ ℓ * ℓ := this
      _ = ℓ ^ 2 := by ring
  have t5 : (d : ℝ) * (A * L) ≤ d * ℓ ^ 2 := mul_le_mul_of_nonneg_left t4 hd0
  have e1 : (1 + (2 * C1 ^ 2 * (lam * d) + 2 * (2 * lT + d * A))) * L
      = L + 2 * (C1 ^ 2 * lam * d * L) + 4 * (lT * L) + 2 * (d * (A * L)) := by ring
  have e2 : (2 * C1 ^ 2 * lam + 7) * d * ℓ ^ 2
      = 2 * (C1 ^ 2 * lam * d * ℓ ^ 2) + 7 * (d * ℓ ^ 2) := by ring
  rw [e1, e2]; linarith

theorem solution (pmax lam C1 : ℝ) (hpmax : 0 < pmax) (hlam : 0 < lam) (hC1 : 0 ≤ C1) :
    ∃ C1' C2' : ℝ, 0 < C1' ∧ 0 < C2' ∧ ∀ d : ℕ, 1 ≤ d → ∀ T0 : ℕ, 1 ≤ T0 →
      Real.sqrt (pmax ^ 2 * max 1 ((C1 * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log T0 +
            d * Real.log ((d * lam + ((T0 : ℝ) - 1) * pmax ^ 2) / (d * lam)))) ^ 2) *
        Real.log ((d * lam + T0 * pmax ^ 2) / (d * lam))) ≤
        C1' * Real.sqrt d * Real.log (C2' * T0) := by
  set a : ℝ := pmax ^ 2 / lam with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha : a * lam = pmax ^ 2 := by rw [ha_def]; field_simp
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hC2 : (0 : ℝ) < Real.exp 1 + a := by positivity
  refine ⟨pmax * Real.sqrt (2 * C1 ^ 2 * lam + 7), Real.exp 1 + a, by positivity, hC2, ?_⟩
  intro d hd T0 hT0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT : (1 : ℝ) ≤ T0 := by exact_mod_cast hT0
  have hdpos : (0 : ℝ) < d := by linarith
  have hTpos : (0 : ℝ) < T0 := by linarith
  have hM : 0 < (d : ℝ) * lam := by positivity
  set ℓ : ℝ := Real.log ((Real.exp 1 + a) * T0) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have : Real.exp 1 ≤ (Real.exp 1 + a) * T0 := by nlinarith
    have h2 := Real.log_le_log (Real.exp_pos 1) this
    rw [Real.log_exp] at h2; exact h2
  have hlogT : Real.log T0 ≤ ℓ := by
    apply Real.log_le_log hTpos; nlinarith
  have hlogT0 : 0 ≤ Real.log T0 := Real.log_nonneg hT
  set L : ℝ := Real.log ((d * lam + T0 * pmax ^ 2) / (d * lam)) with hL
  set A : ℝ := Real.log ((d * lam + ((T0 : ℝ) - 1) * pmax ^ 2) / (d * lam)) with hA
  have hp2 : 0 < pmax ^ 2 := by positivity
  have hA0 : 0 ≤ A := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hM]; nlinarith
  have hAL : A ≤ L := by
    apply Real.log_le_log
    · apply div_pos _ hM; nlinarith
    · apply div_le_div_of_nonneg_right _ hM.le; nlinarith
  have hL0 : 0 ≤ L := le_trans hA0 hAL
  have hLℓ : L ≤ ℓ := by
    apply Real.log_le_log
    · apply div_pos _ hM; nlinarith
    · rw [div_le_iff₀ hM]
      have e1 : (Real.exp 1 + a) * T0 * (d * lam) = Real.exp 1 * T0 * (d * lam) + T0 * d * pmax ^ 2 := by
        rw [← ha]; ring
      rw [e1]
      have h1 : (d : ℝ) * lam ≤ Real.exp 1 * T0 * (d * lam) := by
        have : (1 : ℝ) ≤ Real.exp 1 * T0 := by nlinarith
        nlinarith
      have h2 : (T0 : ℝ) * pmax ^ 2 ≤ T0 * d * pmax ^ 2 := by
        have : (T0 : ℝ) * pmax ^ 2 * 1 ≤ T0 * pmax ^ 2 * d := by
          apply mul_le_mul_of_nonneg_left hd1; positivity
        nlinarith
      linarith
  have hAℓ : A ≤ ℓ := le_trans hAL hLℓ
  -- main bound
  have hy : 0 ≤ 2 * Real.log T0 + d * A := by positivity
  set s := Real.sqrt (lam * d) with hs
  set t := Real.sqrt (2 * Real.log T0 + d * A) with ht
  have hs2 : s ^ 2 = lam * d := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = 2 * Real.log T0 + d * A := Real.sq_sqrt hy
  have hS : (C1 * s + t) ^ 2 ≤ 2 * C1 ^ 2 * (lam * d) + 2 * (2 * Real.log T0 + d * A) := by
    rw [← hs2, ← ht2]; nlinarith [sq_nonneg (C1 * s - t)]
  have hmax : max 1 ((C1 * s + t) ^ 2) ≤ 1 + (2 * C1 ^ 2 * (lam * d) + 2 * (2 * Real.log T0 + d * A)) := by
    apply max_le
    · have : 0 ≤ 2 * C1 ^ 2 * (lam * d) + 2 * (2 * Real.log T0 + d * A) := by positivity
      linarith
    · linarith
  have hmaxnn : 0 ≤ max 1 ((C1 * s + t) ^ 2) := le_trans zero_le_one (le_max_left _ _)
  have key : (1 + (2 * C1 ^ 2 * (lam * d) + 2 * (2 * Real.log T0 + d * A))) * L
      ≤ (2 * C1 ^ 2 * lam + 7) * d * ℓ ^ 2 := by
    exact key_alg C1 lam d ℓ L (Real.log T0) A hlam hd1 hℓ1 hL0 hLℓ hAℓ hlogT
  have hX : pmax ^ 2 * max 1 ((C1 * s + t) ^ 2) * L ≤ (pmax * Real.sqrt (2 * C1 ^ 2 * lam + 7) * Real.sqrt d * ℓ) ^ 2 := by
    have e : (pmax * Real.sqrt (2 * C1 ^ 2 * lam + 7) * Real.sqrt d * ℓ) ^ 2
        = pmax ^ 2 * ((2 * C1 ^ 2 * lam + 7) * d * ℓ ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hdpos.le]; ring
    rw [e]
    have : max 1 ((C1 * s + t) ^ 2) * L ≤ (2 * C1 ^ 2 * lam + 7) * d * ℓ ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_right hmax hL0) key
    calc pmax ^ 2 * max 1 ((C1 * s + t) ^ 2) * L = pmax ^ 2 * (max 1 ((C1 * s + t) ^ 2) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hp2.le
  calc _ ≤ Real.sqrt ((pmax * Real.sqrt (2 * C1 ^ 2 * lam + 7) * Real.sqrt d * ℓ) ^ 2) :=
        Real.sqrt_le_sqrt hX
    _ = pmax * Real.sqrt (2 * C1 ^ 2 * lam + 7) * Real.sqrt d * ℓ :=
        Real.sqrt_sq (by positivity)
