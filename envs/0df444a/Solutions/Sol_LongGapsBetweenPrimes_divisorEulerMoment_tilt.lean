-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_tilt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:16.707938+00:00
-- url     : https://prove2.me/submissions/8fff0ca7-62bb-4860-8046-f8216cf45cb2

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_primeProduct
import Theorems.Thm_LongGapsBetweenPrimes_squarefree_euler_factor_tilt

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hE : ∀ p ∈ ps, (p : ℝ) ^ γ ≤ E) :
    divisorEulerMoment (∏ p ∈ ps, p) γ ≤
      divisorEulerMoment (∏ p ∈ ps, p) 0 *
        Real.exp (E * γ * ∑ p ∈ ps, Real.log p / p) := by
  have h := Finset.prod_le_prod (s := ps)
    (f := fun p : ℕ => 1 + (p : ℝ) ^ γ / ((p : ℝ) - 1))
    (g := fun p : ℕ => (1 + 1 / ((p : ℝ) - 1)) * Real.exp (E * γ * Real.log p / p))
    (fun p hp => by
      have hpm : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (hps p hp).one_lt)
      positivity)
    (fun p hp => squarefree_euler_factor_tilt (by exact_mod_cast (hps p hp).one_lt) hγ (hE p hp))
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h
  have he : (∑ p ∈ ps, E * γ * Real.log p / p) = E * γ * ∑ p ∈ ps, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simpa only [divisorEulerMoment_primeProduct ps hps, Real.rpow_zero, he] using h
end LongGapsBetweenPrimes
