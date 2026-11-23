-- Prove2me | solution 1 for Kyprianou.Ch01.pmfWeightedTanneryRightAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:08:36.149969+00:00
-- url     : https://prove2.me/submissions/dc67b4ea-067e-4be0-b223-cca38c6b5bbc

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (p : PMF ℕ) (f : ℝ → ℕ → ℝ)
    (hpoint : ∀ k : ℕ,
      Tendsto (fun t : ℝ => f t k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ k : ℕ, |f t k| ≤ 1) :
    Tendsto
      (fun t : ℝ => ∑' k : ℕ, (p k).toReal * f t k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hs : Summable (fun k : ℕ => (p k).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have ht (k : ℕ) :
      Tendsto (fun t : ℝ => (p k).toReal * f t k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hpoint k))
  have hb : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ k : ℕ, ‖(p k).toReal * f t k‖ ≤ (p k).toReal := by
    filter_upwards [hbound] with t h k
    calc
      ‖(p k).toReal * f t k‖ =
          (p k).toReal * |f t k| := by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (p k).toReal * 1 :=
        mul_le_mul_of_nonneg_left (h k) ENNReal.toReal_nonneg
      _ = (p k).toReal := mul_one _
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence hs ht hb)

