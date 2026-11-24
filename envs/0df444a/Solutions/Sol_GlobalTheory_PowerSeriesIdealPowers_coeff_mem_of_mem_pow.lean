-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.coeff_mem_of_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:17.328299+00:00
-- url     : https://prove2.me/submissions/063c69bc-4036-4d81-beeb-ab73c3284e02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.PowerSeriesIdealPowers
theorem _root_.solution {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add]; exact add_mem (hx d) (hy d)
end GlobalTheory.PowerSeriesIdealPowers
