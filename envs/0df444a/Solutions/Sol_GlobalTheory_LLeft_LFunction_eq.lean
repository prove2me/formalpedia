-- Prove2me | solution 1 for GlobalTheory.LLeft.LFunction_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:57:44.057995+00:00
-- url     : https://prove2.me/submissions/1f70e1ab-7962-4fda-9108-3f0081aea41f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_differentiable_diffPow
import Theorems.Thm_GlobalTheory_LLeft_abel_three
import Theorems.Thm_GlobalTheory_LLeft_summable_nine_pow_mul_inv_sq_succ
import Theorems.Thm_GlobalTheory_LLeft_norm_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, -(15 / 8 : ℝ) < s.re → LFunction χ s =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hz : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine Finset.sum_bij' (fun n _ => (n : ZMod q)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro x _; simpa using ZMod.val_lt x
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro x _; simp
    · intro n _; rfl
  have hz' : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0 := by
    have h1 := Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q
    rw [Finset.sum_range_succ, hz] at h1
    simp only [CharP.cast_eq_zero, Nat.cast_zero, zero_add] at h1
    exact (add_eq_right.mp h1.symm)
  obtain ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩ := abel_three q hq
    (fun n => χ ((n + 1 : ℕ) : ZMod q)) (fun n => by simp) hz' (fun n => χ.norm_le_one _)
  refine ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, fun s hs => ?_⟩
  set R : ℝ := ‖s‖ + 3 with hR
  set U : Set ℂ := {z | -(15 / 8 : ℝ) < z.re} ∩ Metric.ball 0 R with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hsU : s ∈ U := ⟨hs, by simp [hR]⟩
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by
    simp only [hR, Metric.mem_ball, dist_zero_right, Complex.norm_ofNat]
    linarith [norm_nonneg s]⟩
  have d1 : DifferentiableOn ℂ (fun z => ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left (8 * (q : ℝ) ^ 3 * (R + 3) ^ 3))
      (fun n => ((differentiable_diffPow 3 _ (by positivity)).const_mul _).differentiableOn)
      hUo (fun n z hz => norm_term_le b _ R hb z (le_of_lt hz.1) ?_ n)
    have := hz.2
    simp only [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  have d2 : DifferentiableOn ℂ (fun z => μ₁ * diffPow 0 z 1 + μ₂ * diffPow 1 z 1 +
      μ₃ * diffPow 2 z 1 + ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U :=
    (((((differentiable_diffPow 0 1 one_pos).const_mul _).add
      ((differentiable_diffPow 1 1 one_pos).const_mul _)).add
      ((differentiable_diffPow 2 1 one_pos).const_mul _)).differentiableOn).add d1
  have d3 : DifferentiableOn ℂ (LFunction χ) U := (differentiable_LFunction hχ).differentiableOn
  refine (d3.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (d2.analyticOnNhd hUo)
    hUc h2U ?_ hsU
  have hV : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  filter_upwards [hV] with z hz1
  have hz1' : 1 < z.re := hz1
  rw [← he z hz1', LFunction_eq_LSeries χ hz1', LSeries,
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz1').tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), diffPow, cpow_neg, div_eq_mul_inv]
  push_cast
  rfl
end GlobalTheory.LLeft
