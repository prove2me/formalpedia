-- Prove2me | solution 1 for NoHair.hansen_potential_of_lapse_radius
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:30:54.897838+00:00
-- url     : https://prove2.me/submissions/d2064249-cf9c-4e9f-89dc-1cdcddd8b38b

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem solution (δ : ℝ) (hδ : 0 < δ) (N : ADMPoint → ℝ) (e : ADMPoint → ADMPoint)
    (he : ∀ y ∈ ball (0:ADMPoint) δ, y ≠ 0 → 0 < N (e y) ∧ (1-N (e y))/(1+N (e y)) = ‖y‖) :
    ∃ f : ADMPoint → ℝ, f 0 = 0 ∧ ContDiffOn ℝ ∞ f (ball 0 (min δ 1)) ∧
      (∀ y ∈ ball (0:ADMPoint) (min δ 1), y ≠ 0 → f y = ((N (e y))⁻¹-N (e y))^2/4) ∧
      ∀ y ∈ ball (0:ADMPoint) (min δ 1), f y = 4*‖y‖^2/(1-‖y‖^2)^2 := by
  let f:=fun y : ADMPoint => 4*‖y‖^2/(1-‖y‖^2)^2
  have den {y : ADMPoint} (hy : y∈ball (0:ADMPoint) (min δ 1)) : 0<1-‖y‖^2 := by
    have q:=(lt_min_iff.mp (mem_ball_zero_iff.mp hy)).2
    nlinarith only [mul_pos (sub_pos.mpr q) (show 0<1+‖y‖ by positivity)]
  have sm : ContDiff ℝ ∞ (fun y : ADMPoint => ‖y‖^2) := contDiff_norm_sq ℝ
  refine ⟨f,by simp [f],(contDiffOn_const.mul sm.contDiffOn).div ((contDiffOn_const.sub sm.contDiffOn).pow 2)
    (fun y hy => pow_ne_zero _ (den hy).ne'),?_,fun y _ => rfl⟩
  intro y hy hne
  obtain ⟨p,eq⟩:=he y (ball_subset_ball (min_le_left _ _) hy) hne
  let n:=N (e y)
  let r:=‖y‖
  have pd : 1+n≠0 := by dsimp only [n]; linarith
  have hr : 0≤r := norm_nonneg _
  have ht : r<1 := (lt_min_iff.mp (mem_ball_zero_iff.mp hy)).2
  have pr : (1+r)≠0 := by linarith
  have pm : (1-r)≠0 := by linarith
  have dm : 1-r^2≠0 := (den hy).ne'
  have hn : n=(1-r)/(1+r) := by
    apply (eq_div_iff pr).2
    have e' : 1-n=r*(1+n) := (div_eq_iff pd).mp eq
    linarith only [e',show n*(1+r)=n+n*r by ring,show r*(1+n)=r+n*r by ring]
  change 4*r^2/(1-r^2)^2=(n⁻¹-n)^2/4
  rw [hn,inv_div]
  field_simp [dm,pr,pm] <;> ring
