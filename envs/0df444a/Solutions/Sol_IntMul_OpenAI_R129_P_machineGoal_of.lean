-- Prove2me | solution 1 for IntMul.OpenAI.R129.P.machineGoal_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T13:46:59.240119+00:00
-- url     : https://prove2.me/submissions/a2054841-2c22-4a53-91de-4c9a6b7367b0

import Mathlib
import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace IntMul.OpenAI.R129.P.MG

theorem multipliesAt_mono {M : IntMul.MultitapeTM} {n : ℕ} {τ τ' : ℝ}
    (h : IntMul.MultipliesAt M n τ) (hle : τ ≤ τ') : IntMul.MultipliesAt M n τ' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hle, hh⟩

theorem Ncost_nonneg {p d K ℓ α : ℝ} (hp : 1 ≤ p) (hd : 0 ≤ d) (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ)
    (hα : 0 ≤ α) : 0 ≤ IntMul.OpenAI.R129.Ncost p d K ℓ α := by
  unfold IntMul.OpenAI.R129.Ncost
  have hp0 : 0 ≤ p := by linarith
  have h1 : 0 ≤ Real.logb 2 p := Real.logb_nonneg (by norm_num) hp
  have t1 : 0 ≤ d * K := mul_nonneg hd hK
  have t2 : 0 ≤ p * K ^ (IntMul.OpenAI.R129.τ - 1) := mul_nonneg hp0 (Real.rpow_nonneg hK _)
  have t3 : 0 ≤ ℓ * d ^ IntMul.OpenAI.R129.lam' := mul_nonneg hℓ (Real.rpow_nonneg hd _)
  have t4 : 0 ≤ d ^ 2 * (1 + ℓ ^ IntMul.OpenAI.R129.τ) :=
    mul_nonneg (sq_nonneg d) (by have := Real.rpow_nonneg hℓ IntMul.OpenAI.R129.τ; linarith)
  have t5 : 0 ≤ d * p ^ (1 / 2 + IntMul.OpenAI.R129.δ) * α :=
    mul_nonneg (mul_nonneg hd (Real.rpow_nonneg hp0 _)) hα
  have t6 : 0 ≤ d * p ^ IntMul.OpenAI.R129.δ := mul_nonneg hd (Real.rpow_nonneg hp0 _)
  have t7 : 0 ≤ p ^ IntMul.OpenAI.R129.δ := Real.rpow_nonneg hp0 _
  linarith

end IntMul.OpenAI.R129.P.MG

theorem solution (M : IntMul.MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₁ : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (A : ℕ)
    (htime : ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n → IntMul.MultipliesAt M n
      (C₀ * (IntMul.OpenAI.Glue.VP n * IntMul.OpenAI.R129.Ncost (6 * (IntMul.lg n : ℝ))
        (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.KP n) (IntMul.OpenAI.R129.ℓP n)
        (IntMul.OpenAI.R129.αP n) * (Real.log (6 * (IntMul.lg n : ℝ)) + 1) ^ A + n))) :
    IntMul.OpenAI.R129.P.MachineGoal := by
  refine ⟨M, hcorr, C₀ * 6 ^ A, by positivity, A, max IntMul.OpenAI.Glue.n0 n₁, fun n hn => ?_⟩
  refine IntMul.OpenAI.R129.P.MG.multipliesAt_mono
    (htime n (le_of_max_le_left hn) (le_of_max_le_right hn)) ?_
  set x : ℝ := (IntMul.lg n : ℝ) with hxdef
  set V := IntMul.OpenAI.Glue.VP n
  set N := IntMul.OpenAI.R129.Ncost (6 * x) (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.KP n)
    (IntMul.OpenAI.R129.ℓP n) (IntMul.OpenAI.R129.αP n) with hNdef
  have h1 : 1 ≤ IntMul.lg n := IntMul.OpenAI.Glue.bP_pos n
  have hx : (1 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast h1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num); linarith
  have hl6' : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hsplit : Real.log (6 * x) = Real.log 6 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hb0 : 0 ≤ Real.log (6 * x) + 1 := by rw [hsplit]; linarith
  have hb : Real.log (6 * x) + 1 ≤ 6 * (Real.log x + 1) := by rw [hsplit]; linarith
  have hpow : (Real.log (6 * x) + 1) ^ A ≤ 6 ^ A * (Real.log x + 1) ^ A := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hb0 hb A
  have hV : 0 ≤ V := by
    show 0 ≤ IntMul.OpenAI.Glue.VP n
    unfold IntMul.OpenAI.Glue.VP; positivity
  have hN : 0 ≤ N := IntMul.OpenAI.R129.P.MG.Ncost_nonneg (by linarith) (by positivity)
    (by positivity) (by positivity) (by positivity)
  have h6 : (1 : ℝ) ≤ 6 ^ A := one_le_pow₀ (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hVN : 0 ≤ V * N := mul_nonneg hV hN
  have hq : 0 ≤ (Real.log x + 1) ^ A := by positivity
  calc C₀ * (V * N * (Real.log (6 * x) + 1) ^ A + n)
      ≤ C₀ * (V * N * (6 ^ A * (Real.log x + 1) ^ A) + 6 ^ A * n) := by
        apply mul_le_mul_of_nonneg_left _ hC₀
        have := mul_le_mul_of_nonneg_left hpow hVN
        nlinarith
    _ = C₀ * 6 ^ A * (V * N * (Real.log x + 1) ^ A + n) := by ring
