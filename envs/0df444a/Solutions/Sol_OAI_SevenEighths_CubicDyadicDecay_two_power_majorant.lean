-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.two_power_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:02.441213+00:00
-- url     : https://prove2.me/submissions/45d0988f-143e-44a3-9135-46b049b525c5

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_decay_summable
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_dyadic_decay_bound

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert hi using 1 <;> first | rfl | ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith
end OAI.SevenEighths.CubicDyadicDecay
