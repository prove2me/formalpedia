-- Prove2me | solution 1 for GlobalTheory.BadShare.badBound_numbers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:45.406195+00:00
-- url     : https://prove2.me/submissions/b93c7b6c-76ee-4acb-95a3-1fbf1ff4abed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LogDivSqrtLeFourExp
import Theorems.Thm_GlobalTheory_BadShare_badBound_tail
import Theorems.Thm_GlobalTheory_BadShare_log_div_sqrt_le_four_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ eps C : ℝ, 0 < eps → eps ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (g f m N q : ℝ), Real.exp (8 * x ^ eps) ≤ g → x ^ (2 : ℝ) ≤ f → f ≤ x ^ C → 0 ≤ m → m ≤ x ^ C → x ^ eps ≤ N → N ≤ x ^ C → Real.exp (x ^ (eps / 6)) ≤ q → 100000 ≤ N ∧ 0 ≤ badBound g f m N q ∧ 6 * badBound g f m N q ≤ Real.exp (-(x ^ (eps / 7))) := by
  intro eps C he he1
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (badBound_tail eps C he)
  refine ⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩
  intro x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx8 : 8 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : 20 * |C| + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN : (100000 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hNbig : 100000 ≤ N := by
    have e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    have h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hxN he.le
    linarith
  have hTail := hX1 x hxX1
  have hCe : eps ≤ C := (Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)
  have hC0 : 0 ≤ C := by linarith
  set P := x ^ C with hP
  set E := Real.exp (-(x ^ (eps / 6))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hN0 : 0 < N := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 hC0
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, sq]
  rw [hx2] at hf1
  have hf0 : 0 ≤ f := le_trans (by positivity) hf1
  have he6 : x ^ (eps / 6) ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by rw [← Real.rpow_add hx0]; norm_num
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hsx : x ^ (1 / 2 : ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 he.le
  have hg8 : Real.exp 8 ≤ g := le_trans (Real.exp_le_exp.2 (by linarith)) hg
  have hg2 : 2 ≤ g := by have := Real.add_one_le_exp 8; linarith
  have hg0 : 0 < g := by linarith
  have hEg : 1 ≤ E * g := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * g := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by linarith)) hg) hE0.le
  have hginv : 1 / g ≤ E := by rw [div_le_iff₀ hg0]; linarith
  have hT2 : Real.log g / Real.sqrt g ≤ 4 * E := by
    have h := log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g)
      (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)
    refine h.trans ?_
    rw [hE]
    gcongr
    linarith
  have hLg : 0 ≤ Real.log g / Real.sqrt g :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hEq : 1 ≤ E * q := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * q := mul_le_mul_of_nonneg_left hq hE0.le
  have hqinv : 1 / (4 * q) ≤ E / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogN : 1 + Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hN0]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)
    have h2 : N * 1 ≤ N * (E * g) := mul_le_mul_of_nonneg_left hEg hN0.le
    linarith
  have hT4 : (7 / 8 : ℝ) ^ f ≤ E := by
    rw [Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]
    have hl78 : Real.log (7 / 8) ≤ -(1 / 8) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith
    have h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f := mul_le_mul_of_nonneg_right hl78 hf0
    have h2 : 8 * x ≤ x * x := mul_le_mul_of_nonneg_right hx8 hx0.le
    linarith
  have hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E := by
    have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
    rw [hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hlN : Real.log N ≤ C * Real.log x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log hN0 hN2
    have hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have h1 : x ^ (eps / 6) * (10 * Real.log N) ≤
        x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) := by
      apply mul_le_mul he6h _ (by linarith) hs0
      have : C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left hlx hC0
      linarith
    have h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x := by
      calc x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))
          = 20 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 20 * C * x := by rw [hsq]
    have h3 : 20 * C * x ≤ x * x := by
      have : 20 * C ≤ x := by have := le_abs_self C; linarith
      exact mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have hgm1 : 0 < g - 1 := by linarith
  unfold badBound
  refine ⟨hNbig, ?_, ?_⟩
  · have t1 : 0 ≤ 3 * f / g := div_nonneg (by linarith) hg0.le
    have t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g :=
      div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)
    have t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) hm1)
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
    have t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N))) := (Real.exp_pos _).le
    linarith
  · have b1 : 3 * f / g ≤ 3 * P * E := by
      calc 3 * f / g = 3 * f * (1 / g) := by ring
        _ ≤ 3 * P * E := mul_le_mul (by linarith) hginv (div_nonneg zero_le_one hg0.le) (by linarith)
    have b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E := by
      calc 23 * f * Real.log g / Real.sqrt g = 23 * f * (Real.log g / Real.sqrt g) := by ring
        _ ≤ 23 * P * (4 * E) := mul_le_mul (by linarith) hT2 hLg (by linarith)
        _ = 92 * P * E := by ring
    have b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E) := by
      have hfm : 2 * f * m ≤ 2 * P * P := mul_le_mul (by linarith) hm2 hm1 (by linarith)
      have hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E := by
        have : 2 * N * E ≤ 2 * P * E := mul_le_mul_of_nonneg_right (by linarith) hE0.le
        linarith
      exact mul_le_mul hfm hsum
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E :=
      mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hP0 : 0 ≤ P := by linarith
    have hPP : P ≤ P * P := le_mul_of_one_le_right hP0 hP1
    have hPPP : P * P ≤ P ^ 3 := by
      rw [show P ^ 3 = P * P * P by ring]
      exact le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1
    have c1 : P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le
    have c2 : P * P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right hPPP hE0.le
    have c3 : E ≤ P ^ 3 * E := le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))
    have hnn : 0 ≤ P ^ 3 * E := mul_nonneg (pow_nonneg hP0 3) hE0.le
    linarith
end GlobalTheory.BadShare
