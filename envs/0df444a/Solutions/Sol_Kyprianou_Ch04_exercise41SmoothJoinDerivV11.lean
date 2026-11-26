-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothJoinDerivV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:50:06.691245+00:00
-- url     : https://prove2.me/submissions/023191b6-880a-4481-8383-f42252849fdf

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    let g := fun x : ℝ => fLeft (-p (-x)) - fLeft 0 +
      fRight (p x) - fRight 0
    ContDiff ℝ 1 g ∧ ∀ x, deriv g x =
      deriv fLeft (-p (-x)) * deriv p (-x) +
      deriv fRight (p x) * deriv p x := by
  let g := fun x : ℝ => fLeft (-p (-x)) - fLeft 0 +
      fRight (p x) - fRight 0
  have hpn : ContDiff ℝ 1 (fun x : ℝ => -p (-x)) := (hp.comp contDiff_id.neg).neg
  have hg : ContDiff ℝ 1 g :=
    (((hL.comp hpn).sub contDiff_const).add (hR.comp hp)).sub contDiff_const
  refine ⟨hg,?_⟩
  intro x
  have hp' := (hp.differentiable (by norm_num) (-x)).hasDerivAt
  have hc : HasDerivAt (fun y : ℝ => p (-y)) (deriv p (-x) * (-1)) x :=
    hp'.comp x (hasDerivAt_neg' x)
  have hn0 : HasDerivAt (fun y : ℝ => -p (-y)) ((-1) * (deriv p (-x) * (-1))) x :=
    (hasDerivAt_neg' (p (-x))).comp x hc
  have hn' : HasDerivAt (fun y : ℝ => -p (-y)) (deriv p (-x)) x := by
    simpa only [neg_mul, one_mul, mul_neg, mul_one, neg_neg] using hn0
  have hl := (hL.differentiable (by norm_num) (-p (-x))).hasDerivAt.comp x hn'
  have hr := (hR.differentiable (by norm_num) (p x)).hasDerivAt.comp x
    (hp.differentiable (by norm_num) x).hasDerivAt
  have h := ((hl.sub_const (fLeft 0)).add hr).sub_const (fRight 0)
  exact h.deriv
