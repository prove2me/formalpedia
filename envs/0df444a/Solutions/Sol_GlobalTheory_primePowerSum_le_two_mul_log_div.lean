-- Prove2me | solution 1 for GlobalTheory.primePowerSum_le_two_mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:52.126022+00:00
-- url     : https://prove2.me/submissions/0e6c787e-c77c-4257-88be-608afac48a20

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Theorems.Thm_GlobalTheory_geom_Icc_one_le_two_mul_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (x : ℝ) (hx : 0 < x) (p : ℕ) (hp : p.Prime) :
    Formalism.HermitianLattices.GL2a2.sP x p ≤ 2 * x * Real.log p / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  unfold Formalism.HermitianLattices.GL2a2.sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  have hc : 0 ≤ x * Real.log p := by positivity
  calc ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i)
      ≤ ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), x * Real.log p * (1 / (p : ℝ)) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi1 : i ≠ 0 := by
          have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1
          omega
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        rw [vonMangoldt_apply_pow hi1, vonMangoldt_apply_prime hp]
        calc Real.log p * min 1 (x / ((p ^ i : ℕ) : ℝ))
            ≤ Real.log p * (x / ((p ^ i : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
          _ = x * Real.log p * (1 / (p : ℝ)) ^ i := by
              push_cast
              rw [one_div_pow]
              ring
    _ ≤ ∑ i ∈ Icc 1 N, x * Real.log p * (1 / (p : ℝ)) ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
    _ = x * Real.log p * ∑ i ∈ Icc 1 N, (1 / (p : ℝ)) ^ i := by rw [Finset.mul_sum]
    _ ≤ x * Real.log p * (2 * (1 / (p : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have h := geom_Icc_one_le_two_mul_sub _ hr0 hr1 N
        have : 0 ≤ (1 / (p : ℝ)) ^ (N + 1) := pow_nonneg hr0 _
        linarith
    _ = 2 * x * Real.log p / p := by ring
end GlobalTheory
