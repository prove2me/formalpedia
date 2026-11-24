-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.series_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:53.462848+00:00
-- url     : https://prove2.me/submissions/a460bddd-3254-48a1-bd22-8568f9f2334d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
import Theorems.Thm_GlobalTheory_Lin_LargeMean_term_eq
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pointwise
import Theorems.Thm_GlobalTheory_Lin_LargeMean_norm_tsum_le_of_close
import Theorems.Thm_GlobalTheory_Lin_NonPrimeVonMangoldt_summable_nonPrime_vonMangoldt_div_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.LargeMean
namespace GlobalTheory.Lin.LargeMean
theorem _root_.solution (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r / 2)) :
    r ^ k * ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)),
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)‖ +
      (δ ^ k * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) +
        (4 * r) ^ k * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hq := GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow
  have hP := hasSum_sum_of_ne_finset_zero
    (s := primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)))
    (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0) (fun n hn => if_neg hn)
  have h := norm_tsum_le_of_close hP.summable ((hs.mul_left (δ ^ k)).add (hq.mul_left ((4 * r) ^ k)))
    (pointwise c hc hr hδ K k h1 h2)
  rw [hP.tsum_eq, (hs.mul_left _).tsum_add (hq.mul_left _), tsum_mul_left, tsum_mul_left,
    Finset.sum_congr rfl (fun n hn => if_pos hn)] at h
  refine le_of_eq_of_le ?_ h
  simp_rw [← term_eq]
  rw [tsum_mul_left, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, derSeries]
end GlobalTheory.Lin.LargeMean
