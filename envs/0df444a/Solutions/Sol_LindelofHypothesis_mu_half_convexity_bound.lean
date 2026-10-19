-- Prove2me | solution 1 for LindelofHypothesis.mu_half_convexity_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:57:03.718772+00:00
-- url     : https://prove2.me/submissions/744a3c56-f988-4c91-a4e1-dacdaeaccf50

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_convex
import Theorems.Thm_LindelofHypothesis_mu_eq_zero_of_one_lt
import Theorems.Thm_LindelofHypothesis_mu_one_eq_zero
import Theorems.Thm_LindelofHypothesis_mu_zero_eq_half

open Complex Filter Asymptotics
open scoped ENNReal

open LindelofHypothesis in
theorem solution : 0 ≤ mu (1 / 2) ∧ mu (1 / 2) ≤ ((1 / 4 : ℝ) : EReal) := by
  obtain ⟨f, hf, hmu⟩ := LindelofHypothesis.mu_convex
  have hval : ∀ σ : ℝ, ∀ v : ℝ, mu σ = (v : EReal) → f σ = v := by
    intro σ v h; rw [hmu] at h; exact_mod_cast h
  have h32 : f (3 / 2) = 0 := hval _ 0 (LindelofHypothesis.mu_eq_zero_of_one_lt (3 / 2) (by norm_num))
  have h52 : f (5 / 2) = 0 := hval _ 0 (LindelofHypothesis.mu_eq_zero_of_one_lt (5 / 2) (by norm_num))
  have h1 : f 1 = 0 := hval _ 0 LindelofHypothesis.mu_one_eq_zero
  have h0 : f 0 = 1 / 2 := hval _ _ LindelofHypothesis.mu_zero_eq_half
  have ha := hf.2 (Set.mem_univ (1 / 2)) (Set.mem_univ (5 / 2)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hb := hf.2 (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at ha hb
  rw [show (1 / 2 : ℝ) * (1 / 2) + 1 / 2 * (5 / 2) = 3 / 2 by norm_num, h32, h52] at ha
  rw [show (1 / 2 : ℝ) * 0 + 1 / 2 * 1 = 1 / 2 by norm_num, h0, h1] at hb
  rw [hmu]
  constructor
  · exact_mod_cast (by linarith : (0 : ℝ) ≤ f (1 / 2))
  · exact_mod_cast (by linarith : f (1 / 2) ≤ 1 / 4)
