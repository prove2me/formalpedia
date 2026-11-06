-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.sieve_growth_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:57.232057+00:00
-- url     : https://prove2.me/submissions/489edc80-1790-4590-a2af-65e4a34cc976

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
import Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_two_power_majorant

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  ring
end OAI.SevenEighths.CubicDyadicDecay
