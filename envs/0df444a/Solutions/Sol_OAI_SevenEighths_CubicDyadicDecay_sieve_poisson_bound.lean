-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.sieve_poisson_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:54.297731+00:00
-- url     : https://prove2.me/submissions/c58b7442-e234-474e-9161-c8083f2c706b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_sieve_growth_majorant
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_poisson_small_power_identity

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]
end OAI.SevenEighths.CubicDyadicDecay
