-- Prove2me | solution 1 for MasulloRH.smooth_bilateral_prime_test_preparation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:43:11.793146+00:00
-- url     : https://prove2.me/submissions/b6844577-d214-46db-b09d-2d81de91bf2f

import Mathlib
open MeasureTheory
theorem solution :
    ∃ (a c : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) a ∧
      ContDiff ℝ (⊤ : ℕ∞) c ∧ HasCompactSupport c ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        let J := ∫ x : ℝ, a x * f x * Real.exp (-x/2)
        let g := fun x : ℝ => a x * f x - J * c x
        ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
        (∀ x : ℝ, |x| ≤ 1/8 → g x = 0) ∧
        (∀ x : ℝ, 1/2 ≤ x → g x = f x) ∧
        (∀ x : ℝ, x ≤ -(1/2) → g x = Real.exp x * f x) ∧
        (∫ x : ℝ, g x * Real.exp (-x/2)) = 0 := by
  let a := fun x : ℝ => Real.smoothTransition (4*x-1) + Real.exp x * Real.smoothTransition (-4*x-1)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := by
    dsimp [a]
    exact (Real.smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => 4*x-1))).add
      (Real.contDiff_exp.mul (Real.smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => -4*x-1))))
  let B : ContDiffBump (1/4:ℝ) := ⟨1/32,1/16,by norm_num,by norm_num⟩
  let w := fun x : ℝ => Real.exp (-x/2)
  let wb := fun x : ℝ => B x * w x
  have hwb : Continuous wb := B.continuous.mul (by dsimp [w]; fun_prop)
  have hwbs : HasCompactSupport wb := B.hasCompactSupport.mul_right
  let m := ∫ x : ℝ, wb x
  have hBc : B (1/4:ℝ) = 1 := B.one_of_mem_closedBall (by simp [Metric.mem_closedBall,B])
  have hm : 0 < m := hwb.integral_pos_of_hasCompactSupport_nonneg_nonzero hwbs
    (fun x => mul_nonneg B.nonneg (Real.exp_pos _).le) (by
      change B (1/4:ℝ) * Real.exp _ ≠ 0
      rw [hBc,one_mul]
      exact (Real.exp_pos _).ne')
  let c := fun x : ℝ => m⁻¹ * B x
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := contDiff_const.mul B.contDiff
  have hcs : HasCompactSupport c := B.hasCompactSupport.mul_left
  have hcz (x : ℝ) (hx : (1/16:ℝ) ≤ |x-1/4|) : c x = 0 := by
    have hb : B x = 0 := B.zero_of_le_dist (by simpa [B, Real.dist_eq] using hx)
    simp [c,hb]
  refine ⟨a,c,ha,hc,hcs,?_⟩
  intro f hf hfs
  dsimp only
  let J := ∫ x : ℝ, a x * f x * Real.exp (-x/2)
  change ContDiff ℝ _ (fun x => a x*f x-J*c x) ∧ _
  refine ⟨(ha.mul hf).sub (contDiff_const.mul hc),
    (hfs.mul_left (f := a)).sub (hcs.mul_left (f := fun _ => J)),?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨hl,hr⟩ := abs_le.mp hx
    have hz := hcz x (by linarith [neg_le_abs (x-1/4)])
    simp only [a,Real.smoothTransition.zero_of_nonpos (by linarith : 4*x-1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : -4*x-1 ≤ 0),hz, mul_zero,sub_zero,zero_mul,add_zero,one_mul,zero_add,mul_one]
  · intro x hx
    have hz := hcz x (by linarith [le_abs_self (x-1/4)])
    simp only [a, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4*x-1),
      Real.smoothTransition.zero_of_nonpos (by linarith : -4*x-1 ≤ 0),hz, mul_zero,sub_zero,zero_mul,add_zero,one_mul,zero_add,mul_one]
  · intro x hx
    have hz := hcz x (by linarith [neg_le_abs (x-1/4)])
    simp only [a, Real.smoothTransition.zero_of_nonpos (by linarith : 4*x-1 ≤ 0),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ -4*x-1),hz, mul_zero,sub_zero,zero_mul,add_zero,one_mul,zero_add,mul_one]
  · have hi₁ : Integrable (fun x : ℝ => a x * f x * w x) :=
      ((ha.continuous.mul hf.continuous).mul (by dsimp [w]; fun_prop)).integrable_of_hasCompactSupport
        (hfs.mul_left (f := a)).mul_right
    have hi₂ : Integrable (fun x : ℝ => (J*m⁻¹) * wb x) := (hwb.integrable_of_hasCompactSupport hwbs).const_mul (J*m⁻¹)
    change (∫ x : ℝ, (a x * f x - J*c x) * w x) = 0
    calc
      _ = ∫ x : ℝ, a x * f x * w x - (J*m⁻¹) * wb x := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [c,wb]
        ring
      _ = J - (J*m⁻¹)*m := by rw [integral_sub hi₁ hi₂,integral_const_mul]
      _ = 0 := by field_simp [hm.ne'] <;> ring
