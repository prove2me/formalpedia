-- Prove2me | solution 1 for Kyprianou.Ch04.signedAtomicCumulativeDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:41:27.350561+00:00
-- url     : https://prove2.me/submissions/f7fc60e1-0c8f-4df7-b273-98ec2b1ed076

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_atomicCumulativeDerivativeV1
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- Signed absolutely summable atomic sums have derivative zero almost everywhere. -/
theorem solution {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable (fun i => |w i|)) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt
      (fun t => ∑' i, (a ⁻¹' Iic t).indicator w i) 0 x := by
  let p : ι → ℝ := fun i => max 0 (w i)
  let q : ι → ℝ := fun i => max 0 (-w i)
  have hp : Summable p := Summable.of_nonneg_of_le
    (fun i => le_max_left _ _) (fun i => max_le (abs_nonneg _) (le_abs_self _)) hw
  have hq : Summable q := Summable.of_nonneg_of_le
    (fun i => le_max_left _ _) (fun i => max_le (abs_nonneg _) (neg_le_abs _)) hw
  have he : (fun t : ℝ => ∑' i, (a ⁻¹' Iic t).indicator w i) =
      (fun t : ℝ => ∑' i, (a ⁻¹' Iic t).indicator p i) -
        (fun t : ℝ => ∑' i, (a ⁻¹' Iic t).indicator q i) := by
    funext t
    change _ = (∑' i, (a ⁻¹' Iic t).indicator p i) - ∑' i, (a ⁻¹' Iic t).indicator q i
    rw [← (hp.indicator _).tsum_sub (hq.indicator _)]
    congr 1
    funext i
    by_cases hi : a i ∈ Iic t
    · simp only [indicator_of_mem (show i ∈ a ⁻¹' Iic t from hi), p, q]
      by_cases h : 0 ≤ w i
      · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h), sub_zero]
      · rw [max_eq_left (le_of_not_ge h), max_eq_right (neg_nonneg.mpr (le_of_not_ge h))]
        ring
    · simp [indicator_of_notMem (show i ∉ a ⁻¹' Iic t from hi)]
  rw [he]
  filter_upwards [
    Kyprianou.Ch04.atomicCumulativeDerivativeV1 a p hp (fun i => le_max_left _ _),
    Kyprianou.Ch04.atomicCumulativeDerivativeV1 a q hq (fun i => le_max_left _ _)
  ] with x h1 h2
  simpa only [sub_zero] using h1.sub h2
