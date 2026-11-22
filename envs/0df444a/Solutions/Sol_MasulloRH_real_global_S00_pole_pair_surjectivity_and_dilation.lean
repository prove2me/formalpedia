-- Prove2me | solution 1 for MasulloRH.real_global_S00_pole_pair_surjectivity_and_dilation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:20:51.279179+00:00
-- url     : https://prove2.me/submissions/6f590ea5-0675-4c77-a8d6-a3dd49898e18

import Mathlib
open MeasureTheory
theorem solution :
    (∀ A B : ℝ, ∃ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
      (∀ x, h (-x) = h x) ∧ h 0 = A ∧ (∫ x : ℝ, h x) = B) ∧
    (∀ (h : ℝ → ℝ) (s : ℝ),
      let v := fun x : ℝ => Real.exp (-s/2) * h (Real.exp (-s) * x)
      (v 0, ∫ x : ℝ, v x) = (Real.exp (-s/2) * h 0, Real.exp (s/2) * ∫ x : ℝ, h x)) := by
  constructor
  · intro A B
    let g : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
    let k := fun x : ℝ => g (2*x)
    have hg0 : g 0 = 1 := g.one_of_mem_closedBall (by simp [g])
    have hk : ContDiff ℝ (⊤ : ℕ∞) k := by
      exact g.contDiff.comp (contDiff_const.mul contDiff_id)
    have hks : HasCompactSupport k := by
      simpa only [smul_eq_mul] using g.hasCompactSupport.comp_smul (by norm_num : (2:ℝ) ≠ 0)
    let m := ∫ x : ℝ, g x
    have hp : 0 < m := g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      g.hasCompactSupport (fun x => g.nonneg) (by rw [hg0]; norm_num : g 0 ≠ 0)
    have hm : (∫ x : ℝ, k x) = (2:ℝ)⁻¹*m := by
      simpa [k, m, smul_eq_mul] using Measure.integral_comp_mul_left (fun x : ℝ => g x) (2:ℝ)
    let u := 2*B/m-A
    let v := 2*A-2*B/m
    refine ⟨fun x => u*g x+v*k x, (contDiff_const.mul g.contDiff).add (contDiff_const.mul hk),
      ?_, ?_, ?_, ?_⟩
    · rw [hasCompactSupport_iff_eventuallyEq] at hks ⊢
      have hg := hasCompactSupport_iff_eventuallyEq.mp g.hasCompactSupport
      filter_upwards [hg,hks] with x hx hy
      change g x = 0 at hx
      change k x = 0 at hy
      simp [hx,hy]
    · intro x
      simp [k, g.neg, mul_neg]
    · simp [k, hg0, u, v] <;> ring
    · rw [integral_add ((g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).const_mul u)
          ((hk.continuous.integrable_of_hasCompactSupport hks).const_mul v),
          integral_const_mul, integral_const_mul, hm]
      change u*m + v*((2:ℝ)⁻¹*m) = B
      dsimp [u,v]
      field_simp [hp.ne']
      <;> ring
  · intro h s
    dsimp only
    rw [mul_zero, integral_const_mul, Measure.integral_comp_mul_left, Real.exp_neg,
      inv_inv, abs_of_pos (Real.exp_pos s), smul_eq_mul, ← mul_assoc, ← Real.exp_add]
    rw [show -s/2+s=s/2 by ring]
