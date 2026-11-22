-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_covering_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:27.409791+00:00
-- url     : https://prove2.me/submissions/db7111b0-33f7-4039-aaf3-b26b95d56116

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothScaleConstant_pos
import Theorems.Thm_LongGapsBetweenPrimes_eventually_cover_parameters
import Theorems.Thm_LongGapsBetweenPrimes_coverW_le_coverZ
import Theorems.Thm_LongGapsBetweenPrimes_coverZ_le_floor
import Theorems.Thm_LongGapsBetweenPrimes_eventually_greedy_product_bound
import Theorems.Thm_LongGapsBetweenPrimes_combine_greedy_residues
import Theorems.Thm_LongGapsBetweenPrimes_eventually_zeroSurvivors_bound
import Theorems.Thm_LongGapsBetweenPrimes_coverLength_eq
import Theorems.Thm_LongGapsBetweenPrimes_coverEta_pos
import Theorems.Thm_LongGapsBetweenPrimes_coverEta_le_one
import Theorems.Thm_LongGapsBetweenPrimes_coveringConstant_mul_eta_le
import Theorems.Thm_LongGapsBetweenPrimes_eventually_coverLength_bounds
import Theorems.Thm_LongGapsBetweenPrimes_zeroCoverPrimes_subset
import Theorems.Thm_LongGapsBetweenPrimes_zeroCoverPrimes_disjoint

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ a : ℕ → ℕ, (∀ p ∈ ⌊x⌋₊.primesLE, a p < p) ∧
      ((survivors (Finset.Icc 1 (coverLength coverEta x)) ⌊x⌋₊.primesLE a).card : ℝ) ≤
        sieveDelta * x := by
  classical
  filter_upwards [eventually_cover_parameters,
    eventually_coverLength_bounds coverEta_pos coverEta_le_one,
    eventually_zeroSurvivors_bound, eventually_greedy_product_bound]
    with x hparameters hlength hzero hgreedy
  obtain ⟨hx, hL, hLL, hLLL, _, _, _, hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hLLL0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hZ := coverZ_le_floor hx0 hZhigh
  have hW := (coverW_le_coverZ (by linarith) hZlow).trans hZ
  obtain ⟨a, ha, hcard⟩ := combine_greedy_residues
    (Finset.Icc 1 (coverLength coverEta x)) (zeroCoverPrimes x)
    (auxiliaryPrimes (coverW x) (coverZ x)) ⌊x⌋₊.primesLE
    (zeroCoverPrimes_subset hx0.le hW)
    (by
      intro p hp
      obtain ⟨hp, _, hpZ⟩ := mem_auxiliaryPrimes.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpZ.trans hZ, hp⟩)
    (zeroCoverPrimes_disjoint x) (fun p hp => (Nat.mem_primesLE.mp hp).2.pos)
  refine ⟨a, ha, ?_⟩
  have hfloor : (coverLength coverEta x : ℝ) ≤ coverEta * coverScale x := by
    rw [coverLength_eq]
    apply Nat.floor_le
    unfold coverScale
    exact mul_nonneg coverEta_pos.le (by positivity)
  have hzero' := hzero (coverLength coverEta x) hlength.1.le hlength.2.1
  have hC := smoothScaleConstant_pos
  calc
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        ∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ)) := hcard
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) :=
      mul_le_mul_of_nonneg_left hgreedy (Nat.cast_nonneg _)
    _ ≤ ((Real.log 4 + 2) * (coverEta * coverScale x) / Real.log x) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) := by
      gcongr
      exact hzero'.trans (by gcongr)
    _ = (coveringConstant * coverEta) * x := by
      unfold coveringConstant coverScale
      field_simp
    _ ≤ sieveDelta * x := mul_le_mul_of_nonneg_right coveringConstant_mul_eta_le hx0.le
end LongGapsBetweenPrimes
