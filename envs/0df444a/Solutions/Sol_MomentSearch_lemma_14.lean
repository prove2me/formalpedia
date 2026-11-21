-- Prove2me | solution 1 for MomentSearch.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:40:56.503924+00:00
-- url     : https://prove2.me/submissions/611f546e-dab3-43c9-82b5-e0a53f818bc2

import Mathlib
import Definitions.Def_MomentSearch_correctionNorm
import Theorems.Thm_MomentSearch_lemma_12
import Theorems.Thm_MomentSearch_eq_11

open MomentSearch

theorem solution (C₁ : ℝ)
    (hC₁ : ∀ n k : ℕ, 2 ≤ n → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ q : Polynomial ℝ, q.natDegree ≤ k →
      (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) →
      ∀ x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4), |q.eval x| ≤ C₁)
    (n k : ℕ) (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ ((n : ℝ) - 1) / 2) (m m₀ : Fin n)
    (hm : ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) ∧ ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4)
    (hm₀ : ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) ∧ ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4) :
    correctionNorm n k m m₀ ≤
      8 * C₁ / Real.sqrt 5 * ((k : ℝ) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| / ((n : ℝ) - 1)) := by
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by linarith
  have hn : 2 ≤ n := by exact_mod_cast hn'
  have hd : 0 < (n : ℝ) - 1 := by linarith
  obtain ⟨q, hq, hgrid, hvalue⟩ := (MomentSearch.lemma_12 hn k m m₀).1.1
  have hqBound := hC₁ n k hn hk q hq hgrid
  have hCnonneg : 0 ≤ C₁ :=
    (abs_nonneg _).trans (hqBound 0 ⟨by norm_num, by norm_num⟩)
  have hcentral (t : Fin n)
      (ht : ((n : ℝ) - 1) / 4 ≤ ((t : ℕ) : ℝ) ∧
        ((t : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4) :
      grid n (t : ℕ) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [Set.mem_Icc, grid]
    constructor
    · have hl : (1 / 2 : ℝ) ≤ 2 * ((t : ℕ) : ℝ) / ((n : ℝ) - 1) :=
        (le_div_iff₀ hd).2 (by linarith [ht.1])
      linarith
    · have hu : 2 * ((t : ℕ) : ℝ) / ((n : ℝ) - 1) ≤ (3 / 2 : ℝ) :=
        (div_le_iff₀ hd).2 (by linarith [ht.2])
      linarith
  have hroot : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      ‖deriv (fun y : ℝ => q.eval y) x‖ ≤ (k : ℝ) * C₁ / (Real.sqrt 5 / 4) := by
    have hx' : x ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hbern := MomentSearch.eq_11 k q hq (3 / 4) C₁ (by norm_num) hqBound x hx'
    have hrad : (5 / 16 : ℝ) ≤ (3 / 4 : ℝ) ^ 2 - x ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)
      nlinarith only [hprod]
    have hden : Real.sqrt (5 : ℝ) / 4 ≤ Real.sqrt ((3 / 4 : ℝ) ^ 2 - x ^ 2) := by
      have hsquare : (Real.sqrt (5 : ℝ) / 4) ^ 2 = (5 / 16 : ℝ) := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
        norm_num
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
      rw [hsquare, Real.sq_sqrt (by linarith)]
      exact hrad
    rw [Real.norm_eq_abs, (q.hasDerivAt x).deriv]
    exact hbern.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  have hchange :
      |q.eval (grid n (m : ℕ)) - q.eval (grid n (m₀ : ℕ))| ≤
        (k : ℝ) * C₁ / (Real.sqrt 5 / 4) * |grid n (m : ℕ) - grid n (m₀ : ℕ)| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (-(1 / 2 : ℝ)) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun x _ => (q.hasDerivAt x).differentiableAt) hderiv
        (hcentral m₀ hm₀) (hcentral m hm)
  have hspacing :
      |grid n (m : ℕ) - grid n (m₀ : ℕ)| =
        2 * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| / ((n : ℝ) - 1) := by
    have hdiff : grid n (m : ℕ) - grid n (m₀ : ℕ) =
        2 * (((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)) / ((n : ℝ) - 1) := by
      unfold grid
      ring
    rw [hdiff, abs_div, abs_mul, abs_of_pos hd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hvalue]
  refine (le_abs_self _).trans (hchange.trans_eq ?_)
  rw [hspacing]
  field_simp [hroot.ne', hd.ne']
  ring
