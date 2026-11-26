-- Prove2me | solution 1 for MasulloRH.second_deriv_finite_translated_sum
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:29:20.381256+00:00
-- url     : https://prove2.me/submissions/d0bdbeed-74ee-416e-842f-de083b3af743

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

theorem solution {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (c t : ι → ℝ)
    (hs : ∀ i, ContDiff ℝ 2 (f i)) (x : ℝ) :
    deriv (deriv (fun u => ∑ i, c i * f i (u-t i))) x =
      ∑ i, c i * deriv (deriv (f i)) (x-t i) := by
  have first {g : ι → ℝ → ℝ} (h : ∀ i, Differentiable ℝ (g i)) (z : ℝ) :
      HasDerivAt (fun u => ∑ i, c i * g i (u-t i)) (∑ i, c i * deriv (g i) (z-t i)) z := by
    apply HasDerivAt.fun_sum
    intro i _
    have ht : HasDerivAt (fun u : ℝ => u-t i) 1 z := (hasDerivAt_id z).sub_const (t i)
    simpa only [mul_one, Function.comp_def] using
      (((h i (z-t i)).hasDerivAt.comp z ht).const_mul (c i))
  have h1 : deriv (fun u => ∑ i, c i * f i (u-t i)) =
      fun z => ∑ i, c i * deriv (f i) (z-t i) :=
    funext fun z => (first (fun i => (hs i).differentiable (by decide)) z).deriv
  rw [h1]
  exact (first (fun i => (hs i).differentiable_deriv_two) x).deriv
