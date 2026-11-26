-- Prove2me | solution 1 for MasulloRH.scalar_curvature_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:35:28.380477+00:00
-- url     : https://prove2.me/submissions/8cd105d9-1cac-4a80-9b23-df57a08f3af2

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

private theorem upper_of_second_derivative (g g' g'' : ℝ → ℝ) (l r M A : ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hcurv : ∀ x ∈ Icc l r, -M ≤ g'' x) (hl : g l ≤ A) (hr : g r ≤ A)
    (x : ℝ) (hx : x ∈ Icc l r) : g x ≤ A + M/2 * (x-l)*(r-x) := by
  let v (t : ℝ) := g t + M/2 * ((t-l)*(t-r))
  let v' (t : ℝ) := g' t + M/2 * ((t-r)+(t-l))
  have dv (t : ℝ) : HasDerivAt v (v' t) t := by
    have hd := (((hasDerivAt_id t).sub_const l).mul ((hasDerivAt_id t).sub_const r)).const_mul (M/2)
    convert (hg t).add hd using 1 <;> first | rfl | simp [v']
  have ddv (t : ℝ) : HasDerivAt v' (g'' t + M) t := by
    have hd := (((hasDerivAt_id t).sub_const r).add ((hasDerivAt_id t).sub_const l)).const_mul (M/2)
    convert (hg' t).add hd using 1 <;> first | rfl | ring
  have cv : ConvexOn ℝ (Icc l r) v := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l r)
      (fun t _ => (dv t).continuousAt.continuousWithinAt)
      (fun t _ => (dv t).hasDerivWithinAt) (fun t _ => (ddv t).hasDerivWithinAt)
    intro t ht
    linarith [hcurv t (interior_subset ht)]
  have hle := hx.1.trans hx.2
  have hv := cv.le_max_of_mem_Icc (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hx
  simp only [v, sub_self, zero_mul, mul_zero, add_zero] at hv
  linarith [hv.trans (max_le hl hr)]

theorem solution (f f' f'' : ℝ → ℝ) (l r M A : ℝ) (hM : 0 ≤ M)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hc : ∀ x ∈ Icc l r, |f'' x| ≤ M)
    (hl : |f l| ≤ A) (hr : |f r| ≤ A) (x : ℝ) (hx : x ∈ Icc l r) :
    |f x| ≤ A + M * (r-l)^2 / 8 := by
  have hi := upper_of_second_derivative f f' f'' l r M A hd hdd
    (fun t ht => (abs_le.mp (hc t ht)).1) (abs_le.mp hl).2 (abs_le.mp hr).2 x hx
  have lo := upper_of_second_derivative (fun t => -f t) (fun t => -f' t) (fun t => -f'' t)
    l r M A (fun t => (hd t).neg) (fun t => (hdd t).neg)
    (fun t ht => neg_le_neg (abs_le.mp (hc t ht)).2)
    (neg_le.mpr (abs_le.mp hl).1) (neg_le.mpr (abs_le.mp hr).1) x hx
  have pad : M/2 * (x-l)*(r-x) ≤ M * (r-l)^2 / 8 := by
    nlinarith [mul_nonneg hM (sq_nonneg (2*x-l-r))]
  apply abs_le.mpr
  constructor <;> linarith
