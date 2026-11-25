-- Prove2me | solution 1 for Kyprianou.Ch04.bvSummableDominatedFiniteTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:45:11.736297+00:00
-- url     : https://prove2.me/submissions/79a9ff0f-e84f-4b9e-9281-ecc9a27ff098

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (g b : I → ℝ) (hb : Summable b)
    (h : ∀ i, |g i| ≤ b i) (S : Finset I) :
    |(∑' i, g i) - ∑ i ∈ S, g i| ≤ (∑' i, b i) - ∑ i ∈ S, b i := by
  classical
  have hg : Summable g := hb.of_norm_bounded (fun i => by simpa [Real.norm_eq_abs] using h i)
  have hgs := hg.sum_add_tsum_subtype_compl S
  have hbs := hb.sum_add_tsum_subtype_compl S
  have hs : Summable (fun i : {i : I // i ∉ S} => b i) := hb.subtype _
  have hnorm : |∑' i : {i : I // i ∉ S}, g i| ≤ ∑' i : {i : I // i ∉ S}, b i := by
    simpa only [Real.norm_eq_abs] using
      (tsum_of_norm_bounded (f := fun i : {i : I // i ∉ S} => g i) hs.hasSum
        (fun i => by simpa only [Real.norm_eq_abs] using h i))
  rw [← hgs, ← hbs]
  simpa using hnorm
