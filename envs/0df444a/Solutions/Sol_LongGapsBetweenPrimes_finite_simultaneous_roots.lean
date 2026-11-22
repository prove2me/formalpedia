-- Prove2me | solution 1 for LongGapsBetweenPrimes.finite_simultaneous_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:15.457382+00:00
-- url     : https://prove2.me/submissions/e155e0b6-8a1f-440e-88b1-c7a0ad2cf772

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one
import Theorems.Thm_LongGapsBetweenPrimes_diagonalMass_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_residueWeight_second_moment_bound
import Theorems.Thm_LongGapsBetweenPrimes_residueWeight_interval_error
import Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_interval_error
import Theorems.Thm_LongGapsBetweenPrimes_exists_simultaneous_root_of_moments
import Theorems.Thm_LongGapsBetweenPrimes_uncoveredBound_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_normalized_bound
import Theorems.Thm_LongGapsBetweenPrimes_diagonalMass_normalized_lower

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P M k T : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (hM : 1 < M) (hT : 0 < T) (hmin : ∀ p ∈ P.primeFactors, M < p)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (htail : D ^ (-β) * Real.exp (((k + 1 : ℕ) : ℝ) * C * β) +
      16 * (((k + 1 : ℕ) : ℝ)) ^ 2 / M ≤ 1 / 2)
    (hgram : gramBound (k + 1) M D ≤ 5 / 4)
    (herr : 16 * D ^ 6 / T ≤ 1 / 8)
    (hbad : (((k + 1 : ℕ) : ℝ)) * (uncoveredBound k β C M D + 16 * D ^ 6 / T) < 1 / 4) :
    ∃ n < T, ∀ i : Fin (k + 1), ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  have hmin' : ∀ p ∈ P.primeFactors, (M : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (hmin p hp).le
  let A := coefficientMoment P 0 ^ (k + 1)
  have hbase := coefficientMoment_ge_one h.squarefree.ne_zero 0
  have hA : 1 ≤ A := one_le_pow₀ hbase
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hdiag : A / 2 ≤ diagonalMass P (k + 1) D := by
    have hlower := diagonalMass_normalized_lower (k := k + 1) h hβ hD0 (by omega) hmin
    change (1 - _) * A ≤ _ at hlower
    nlinarith only [hlower, mul_le_mul_of_nonneg_right htail hA0.le]
  apply exists_simultaneous_root_of_moments (D := D) root
    (L := A / 4) (U := (uncoveredBound k β C M D + 16 * D ^ 6 / T) * A)
  · have hmoment := (abs_le.mp (residueWeight_second_moment_bound (D := D) h.squarefree
      (Nat.succ_pos k) hM' hmin' root hroot)).1
    have herror := (abs_le.mp
      (residueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one)).1
    have hgram' := mul_le_mul_of_nonneg_right hgram (diagonalMass_nonneg P (k + 1) D)
    unfold gramBound at hgram'
    nlinarith only [hmoment, herror, hgram', hdiag, herr, hA]
  · intro i
    have hscale : coefficientMoment P 0 ^ k ≤ A := by
      simpa only [A, pow_succ] using
        le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hbase) k) hbase
    have hmoment := (replacedResidueWeight_normalized_bound h hβ hD0 hM' hmin' root hroot i).trans
      (mul_le_mul_of_nonneg_left hscale (uncoveredBound_nonneg k β C M hD0.le))
    have herror := (abs_le.mp
      (replacedResidueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one i)).2
    have he0 : 0 ≤ 16 * D ^ 6 / (T : ℝ) := by positivity
    nlinarith only [hmoment, herror, mul_le_mul_of_nonneg_left hA he0]
  · nlinarith only [mul_lt_mul_of_pos_right hbad hA0]
end LongGapsBetweenPrimes
