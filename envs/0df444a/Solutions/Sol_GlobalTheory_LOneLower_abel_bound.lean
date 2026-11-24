-- Prove2me | solution 1 for GlobalTheory.LOneLower.abel_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:35.67383+00:00
-- url     : https://prove2.me/submissions/4c9779e9-6083-4a80-8ee7-be1ff0fcee61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution (a : ℕ → ℂ) (b : ℕ → ℝ) (M : ℝ) (hA : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ M)
    (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, a n * (b n : ℂ)‖ ≤ M * b 0 := by
  have key : ∀ N, ‖∑ n ∈ Finset.range N, a n * (b n : ℂ)
      - (∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * (b 0 - b N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have e : ∑ n ∈ Finset.range (N+1), a n * (b n : ℂ)
          - (∑ n ∈ Finset.range (N+1), a n) * (b (N+1) : ℂ)
          = (∑ n ∈ Finset.range N, a n * (b n : ℂ) - (∑ n ∈ Finset.range N, a n) * (b N : ℂ))
            + (∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        ring
      rw [e]
      have h1 : 0 ≤ b N - b (N+1) := sub_nonneg.2 (hb (Nat.le_succ N))
      have h2 : ‖(∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ)‖
          ≤ M * (b N - b (N+1)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]
        exact mul_le_mul_of_nonneg_right (hA _) h1
      have := norm_add_le (∑ n ∈ Finset.range N, a n * (b n : ℂ)
        - (∑ n ∈ Finset.range N, a n) * (b N : ℂ))
        ((∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ))
      linarith
  have h2 : ‖(∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * b N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 N)]
    exact mul_le_mul_of_nonneg_right (hA _) (hb0 N)
  have h3 := norm_sub_norm_le (∑ n ∈ Finset.range N, a n * (b n : ℂ))
    ((∑ n ∈ Finset.range N, a n) * (b N : ℂ))
  have := key N
  linarith
end GlobalTheory.LOneLower
