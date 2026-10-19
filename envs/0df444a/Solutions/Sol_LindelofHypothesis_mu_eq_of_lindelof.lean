-- Prove2me | solution 1 for LindelofHypothesis.mu_eq_of_lindelof
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:10:29.102328+00:00
-- url     : https://prove2.me/submissions/154b46f5-8469-4972-ba5d-37ff3a580654

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_convex
import Theorems.Thm_LindelofHypothesis_mu_eq_zero_of_one_lt
import Theorems.Thm_LindelofHypothesis_mu_functional_equation

open Complex Filter Asymptotics
open scoped ENNReal

open LindelofHypothesis in
theorem solution (hL : RiemannVonMangoldt.LindelofHypothesis) (σ : ℝ) :
    mu σ = ((max 0 (1 / 2 - σ) : ℝ) : EReal) := by
  obtain ⟨f, hf, hmu⟩ := LindelofHypothesis.mu_convex
  have hval : ∀ x : ℝ, ∀ v : ℝ, mu x = (v : EReal) → f x = v := by
    intro x v h; rw [hmu] at h; exact_mod_cast h
  have hgt : ∀ x : ℝ, 1 < x → f x = 0 := fun x hx =>
    hval x 0 (LindelofHypothesis.mu_eq_zero_of_one_lt x hx)
  -- f ≥ 0 everywhere
  have hnn : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    rcases lt_or_ge 1 x with hx | hx
    · rw [hgt x hx]
    · set t := 1 / (3 - x) with ht
      have hd : 0 < 3 - x := by linarith
      have ht0 : 0 < t := by positivity
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hd]; linarith
      have hc := hf.2 (Set.mem_univ x) (Set.mem_univ 3) ht0.le (show 0 ≤ 1 - t by linarith)
        (by ring)
      simp only [smul_eq_mul] at hc
      have e : t * x + (1 - t) * 3 = 2 := by rw [ht]; field_simp; ring
      rw [e, hgt 2 (by norm_num), hgt 3 (by norm_num)] at hc
      nlinarith
  -- μ(1/2) ≤ 0 from LH
  have hhalf : f (1 / 2) = 0 := by
    have hle : mu (1 / 2) ≤ 0 := by
      unfold mu
      refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
      obtain ⟨r, hr0, hrb⟩ := EReal.lt_iff_exists_real_btwn.mp hb
      have hr : (0 : ℝ) < r := by exact_mod_cast hr0
      have hmem : r ∈ {a : ℝ | (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop]
          (fun T : ℝ => T ^ a)} := by
        show (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop] (fun T : ℝ => T ^ r)
        have := hL r hr
        simpa using this
      exact (sInf_le (Set.mem_image_of_mem _ hmem)).trans hrb.le
    rw [hmu] at hle
    have : f (1 / 2) ≤ 0 := by exact_mod_cast hle
    linarith [hnn (1 / 2)]
  have hzero : ∀ x : ℝ, 1 / 2 ≤ x → f x = 0 := by
    intro x hs
    rcases lt_or_ge 1 x with h1 | h1
    · exact hgt x h1
    · have hc := hf.2 (Set.mem_univ (1 / 2)) (Set.mem_univ 2)
        (show 0 ≤ (2 - x) / (3 / 2) by apply div_nonneg <;> linarith)
        (show 0 ≤ (x - 1 / 2) / (3 / 2) by apply div_nonneg <;> linarith) (by ring)
      simp only [smul_eq_mul] at hc
      have e : (2 - x) / (3 / 2) * (1 / 2) + (x - 1 / 2) / (3 / 2) * 2 = x := by ring
      rw [e, hhalf, hgt 2 (by norm_num)] at hc
      linarith [hnn x]
  rw [hmu]
  congr 1
  rcases le_or_gt (1 / 2) σ with hs | hs
  · rw [max_eq_left (by linarith)]
    exact hzero σ hs
  · rw [max_eq_right (by linarith)]
    have hfe := LindelofHypothesis.mu_functional_equation σ
    rw [hmu, hmu, hzero (1 - σ) (by linarith), ← EReal.coe_add] at hfe
    have : f σ = 0 + (1 / 2 - σ) := by exact_mod_cast hfe
    linarith
