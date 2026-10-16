-- Prove2me | solution 1 for OAI.ShortEgyptian.smooth_divisor_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:58:58.049542+00:00
-- url     : https://prove2.me/submissions/284ab433-6f63-47b9-8777-37e219c22891

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean:L96-L121
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.smooth_divisor_weight. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Theorems.Thm_OAI_ShortEgyptian_polynomial_geom_local
import Theorems.Thm_OAI_ShortEgyptian_prime_rpow_small

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem divisorWeight_one (r : ℕ) (σ : ℝ) : divisorWeight r σ 1 = 1 := by
  simp [divisorWeight]

theorem divisorWeight_mul (r : ℕ) (σ : ℝ) {m n : ℕ} (h : m.Coprime n) :
    divisorWeight r σ (m*n) = divisorWeight r σ m * divisorWeight r σ n := by
  simp only [divisorWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem divisorWeight_prime_pow (r : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    divisorWeight r σ (p^j) = ((j+1:ℕ):ℝ)^r * ((p:ℝ)^(-σ))^j := by
  have hcard : (p^j).divisors.card = j+1 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    exact ArithmeticFunction.sigma_zero_apply_prime_pow hp
  simp only [divisorWeight, hcard, Nat.cast_pow]
  congr 1
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg _)]

theorem divisorWeight_prime_summable (r : ℕ) {σ : ℝ} (hσ : 1/2 ≤ σ)
    {p : ℕ} (hp : p.Prime) : Summable (fun j : ℕ => ‖divisorWeight r σ (p^j)‖) := by
  simp_rw [divisorWeight_prime_pow r σ hp]
  have hx := prime_rpow_small hp hσ
  have hnonneg (j : ℕ) : 0 ≤ ((j+1:ℕ):ℝ)^r * ((p:ℝ)^(-σ))^j := by positivity
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
  exact (polynomial_geom_local r _ hx.1.le hx.2).1

theorem smooth_divisor_weight (r : ℕ) {σ : ℝ} (hσ : 1/2 ≤ σ)
    (s P : Finset ℕ) (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P) :
    ∑ d ∈ s, divisorWeight r σ d ≤
      Real.exp (momentSeriesConst r * ∑ p ∈ P with p.Prime, (p:ℝ)^(-σ)) := by
  classical
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (divisorWeight_one r σ) (fun h => divisorWeight_mul r σ h)
    (fun hp => divisorWeight_prime_summable r hσ hp) P
  have hnn (d : ℕ) : 0 ≤ divisorWeight r σ d := by
    unfold divisorWeight
    positivity
  calc
    _ = ∑ d ∈ s.subtype (· ∈ Nat.factoredNumbers P), divisorWeight r σ d :=
      (sum_subtype_of_mem _ hs).symm
    _ ≤ ∏ p ∈ P with p.Prime, ∑' j : ℕ, divisorWeight r σ (p^j) :=
      sum_le_hasSum _ (fun d _ => hnn d) he.2
    _ ≤ ∏ p ∈ P with p.Prime, Real.exp (momentSeriesConst r * (p:ℝ)^(-σ)) := by
      apply prod_le_prod
      · intro p _
        exact tsum_nonneg (fun j => hnn (p^j))
      · intro p hp
        have hp' := (mem_filter.mp hp).2
        simp_rw [divisorWeight_prime_pow r σ hp']
        exact (polynomial_geom_local r _ (prime_rpow_small hp' hσ).1.le
          (prime_rpow_small hp' hσ).2).2
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.smooth_divisor_weight := @_root_.OAI.ShortEgyptian.smooth_divisor_weight
