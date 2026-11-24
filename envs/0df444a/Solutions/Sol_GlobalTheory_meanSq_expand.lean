-- Prove2me | solution 1 for GlobalTheory.meanSq_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:04.396874+00:00
-- url     : https://prove2.me/submissions/8389fa2d-6628-400c-98dd-8c0d4a04fa83

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart

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
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution (I PPs : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ) (hκ : ∀ n, ‖κ n‖ ≤ 1) :
    (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) / PPs.card ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
  have h1 : ((∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n * c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [jacobiSym.mul_left]
    simp only [map_mul, Complex.conj_ofReal, map_intCast]
    push_cast
    ring
  have h2 : (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc n) (hc n'))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_of_le_one_right (mul_nonneg (hc n) (hc n'))
      (mul_le_one₀ (hκ n) (norm_nonneg _) (hκ n'))
  refine (div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)).trans (le_of_eq ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [abs_div, Nat.abs_cast, mul_div_assoc]
end GlobalTheory
