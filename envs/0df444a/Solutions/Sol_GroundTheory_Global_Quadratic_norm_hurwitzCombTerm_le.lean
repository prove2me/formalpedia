-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.norm_hurwitzCombTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:23:13.61725+00:00
-- url     : https://prove2.me/submissions/8a20861b-a1d5-406c-b082-8a01e25a26a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_norm_taylor_two_le
import Theorems.Thm_GroundTheory_Global_Quadratic_rpow_le_of_exponent_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ‖hurwitzCombTerm x n s‖ ≤
      18 * (((n : ℝ) + min x (1 / 2)) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + min x (1 / 2)) ^ (-(9 / 2) : ℝ)) := by
  set x₀ := min x (1 / 2) with hx₀
  have hx₀0 : 0 < x₀ := lt_min hx0 (by norm_num)
  set B := ((n : ℝ) + x₀) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + x₀) ^ (-(9 / 2) : ℝ) with hB
  have hs1 : ‖s - 1‖ < 3 / 2 := by simpa [dist_eq_norm] using hs
  have hre : |s.re - 1| < 3 / 2 := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hsn : ‖s‖ ≤ 5 / 2 := by
    have := norm_sub_norm_le s 1
    rw [norm_one] at this
    linarith
  have hsn1 : ‖s + 1‖ ≤ 7 / 2 := by
    have h1 : s + 1 = (s - 1) + 2 := by ring
    rw [h1]
    have := norm_add_le (s - 1) 2
    rw [Complex.norm_two] at this
    linarith

  have hM : ∀ t ∈ Icc x₀ 1, ‖s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2)‖ ≤ 9 * B := by
    intro t ht
    have hpos' : 0 < (n : ℝ) + t := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (hx₀0.trans_le ht.1)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos']
    have hre' : (-s - 2).re = -s.re - 2 := by simp
    rw [hre']
    have hb := rpow_le_of_exponent_mem (b := (n : ℝ) + t) (e := -s.re - 2)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hx₀0) (by linarith [ht.1])
      (by linarith [(abs_lt.1 hre).2]) (by linarith [(abs_lt.1 hre).1])
    have hB0 : 0 ≤ B := by positivity
    calc ‖s‖ * ‖s + 1‖ * ((n : ℝ) + t) ^ (-s.re - 2) ≤ (5 / 2) * (7 / 2) * B := by
          gcongr
      _ ≤ 9 * B := by nlinarith
  have hsub : ∀ c ∈ ({x, 1} : Set ℝ), uIcc (1 / 2) c ⊆ Icc x₀ 1 := by
    intro c hc
    refine uIcc_subset_Icc ⟨min_le_right _ _, by norm_num⟩ ?_
    rcases hc with rfl | rfl
    · exact ⟨min_le_left _ _, hx1.le⟩
    · exact ⟨by linarith [min_le_right x (1 / 2)], le_rfl⟩
  have hT : ∀ c ∈ ({x, 1} : Set ℝ), ‖(((n : ℝ) + c : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
      (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((c - 1 / 2 : ℝ) : ℂ)‖ ≤ 9 * B := by
    intro c hc
    have h := norm_taylor_two_le n s (a := 1 / 2) (b := c) (M := 9 * B)
      (fun t ht ↦ add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (hx₀0.trans_le (hsub c hc ht).1))
      (fun t ht ↦ hM t (hsub c hc ht))
    have hc' : |c - 1 / 2| ^ 2 ≤ 1 := by
      rcases hc with rfl | rfl
      · rw [sq_abs]
        nlinarith
      · norm_num
    have hB0 : 0 ≤ 9 * B := by positivity
    calc _ ≤ 9 * B * |c - 1 / 2| ^ 2 := h
      _ ≤ 9 * B * 1 := by gcongr
      _ = 9 * B := mul_one _
  have heq : hurwitzCombTerm x n s =
      ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((x - 1 / 2 : ℝ) : ℂ)) +
      ((1 - 2 * x : ℝ) : ℂ) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((1 - 1 / 2 : ℝ) : ℂ)) := by
    simp only [hurwitzCombTerm]
    push_cast
    ring
  have hc2 : ‖((1 - 2 * x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rw [heq]
  calc _ ≤ 9 * B + 1 * (9 * B) := by
        refine (norm_add_le _ _).trans (add_le_add (hT x (by simp)) ?_)
        rw [norm_mul]
        exact mul_le_mul hc2 (hT 1 (by simp)) (norm_nonneg _) zero_le_one
    _ = 18 * B := by ring
end GroundTheory.Global.Quadratic
