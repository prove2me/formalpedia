-- Prove2me | solution 1 for Kawahira.xi_eq_zero_iff_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:48:13.534156+00:00
-- url     : https://prove2.me/submissions/52ac3fe6-39cf-43cf-8588-7f9c2ac136c2

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_xi_one_sub

open Complex Topology
open Kawahira

theorem solution (s : ℂ) (hs0 : s ≠ 0) :
    xi s = 0 ↔ IsNontrivialZero s := by
  constructor
  · intro hxi
    have hs1 : s ≠ 1 := by
      intro hs
      subst s
      norm_num [xi] at hxi
    have htrivial : ∀ n : ℕ, s ≠ -2 * (n + 1) := by
      intro n hsn
      let t : ℂ := 1 - s
      have ht0 : t ≠ 0 := by
        intro ht
        have hre := congrArg Complex.re ht
        norm_num [t, hsn] at hre
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      have ht1 : t ≠ 1 := by
        intro ht
        have hre := congrArg Complex.re ht
        norm_num [t, hsn] at hre
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      have htre : 1 < t.re := by
        dsimp [t]
        rw [hsn]
        norm_num
        positivity
      have hG : Gammaℝ t ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans (by norm_num) htre)
      have hz : riemannZeta t ≠ 0 := by
        intro hz
        exact riemannZeta_ne_zero_of_one_le_re htre.le hz
      have hC : completedRiemannZeta t ≠ 0 := by
        intro hC
        apply hz
        rw [riemannZeta_def_of_ne_zero ht0, hC, zero_div]
      have hxit : xi t = 0 := by
        dsimp [t]
        rw [xi_one_sub, hxi]
      rw [xi_eq_completed t ht0 ht1] at hxit
      exact (mul_ne_zero (div_ne_zero (mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1)))
        two_ne_zero) hC) hxit
    have hG : Gammaℝ s ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
      intro n hn
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · apply htrivial n
        rw [hn]
        push_cast
        ring
    have hfactor : s * (1 - s) / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) two_ne_zero
    have hC : completedRiemannZeta s = 0 := by
      rw [xi_eq_completed s hs0 hs1] at hxi
      exact (mul_eq_zero.mp hxi).resolve_left hfactor
    refine ⟨?_, htrivial⟩
    rw [riemannZeta_def_of_ne_zero hs0, hC, zero_div]
  · intro hs
    have hstrip := nontrivial_zero_mem_strip s hs.1 hs.2
    have hs1 : s ≠ 1 := by
      intro hone
      subst s
      norm_num at hstrip
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hstrip.1
    have hC : completedRiemannZeta s = 0 := by
      have hquot : completedRiemannZeta s / Gammaℝ s = 0 := by
        rw [← riemannZeta_def_of_ne_zero hs0, hs.1]
      exact (div_eq_zero_iff.mp hquot).resolve_right hG
    rw [xi_eq_completed s hs0 hs1, hC, mul_zero]
