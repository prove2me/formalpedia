-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_coverLength_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:50.029612+00:00
-- url     : https://prove2.me/submissions/37553ab5-bb96-434b-b0b7-2f7dc6aa3d1d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothScaleConstant_gt_ten
import Theorems.Thm_LongGapsBetweenPrimes_eventually_cover_parameters
import Theorems.Thm_LongGapsBetweenPrimes_coverLength_eq

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ x : ℝ in Filter.atTop, x < (coverLength η x : ℝ) ∧
      (coverLength η x : ℝ) ≤ x * Real.log x ^ 2 ∧
      (η / 2) * coverScale x ≤ (coverLength η x : ℝ) := by
  filter_upwards [eventually_cover_parameters,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / η)] with x hp hηL
  obtain ⟨hx, hL, hLL, hLLL, hquad, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hden : Real.log (Real.log x) ^ 2 ≤ Real.log x := by
    nlinarith [smoothScaleConstant_gt_ten, sq_nonneg (Real.log (Real.log x))]
  have hlower : x * Real.log x ≤ coverScale x := by
    unfold coverScale
    apply (le_div_iff₀ (sq_pos_of_pos hLL0)).mpr
    calc
      _ ≤ x * Real.log x * Real.log x :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = x * Real.log x ^ 2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLLL
  have hbig : 2 * x ≤ η * coverScale x := by
    calc
      _ ≤ (Real.log x * η) * x :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hηL) hx0.le
      _ = η * (x * Real.log x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower hη.le
  have hscale0 : 0 ≤ coverScale x := (by positivity : 0 ≤ x * Real.log x).trans hlower
  have hupper : η * coverScale x ≤ x * Real.log x ^ 2 := by
    calc
      _ ≤ coverScale x := mul_le_of_le_one_left hscale0 hη1
      _ ≤ _ := by
        unfold coverScale
        apply (div_le_iff₀ (sq_pos_of_pos hLL0)).mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [Real.log_le_sub_one_of_pos hLL0]
  rw [coverLength_eq]
  have hfloor := Nat.lt_floor_add_one (η * coverScale x)
  exact ⟨by linarith, (Nat.floor_le (mul_nonneg hη.le hscale0)).trans hupper,
    by linarith⟩
end LongGapsBetweenPrimes
