-- Prove2me | solution 1 for LogLogJam.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:10:05.413056+00:00
-- url     : https://prove2.me/submissions/4c3993e2-21ee-4c87-9edc-d54afc6e7bc3

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

set_option autoImplicit false

open LogLogJam

private lemma fStep_mono {x y : ℝ} (hxy : x ≤ y) : fStep x ≤ fStep y := by
  unfold fStep
  have := Real.sqrt_le_sqrt hxy
  linarith

private lemma fStep_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fStep x := by
  unfold fStep
  have := Real.sqrt_nonneg x
  linarith

theorem solution (N : ℝ) (hN : 1 < N) (t : ℕ) (ht : (t : ℝ) ≤ Real.logb 2 (Real.logb 2 N)) :
    fIter t (1 / N) ≤ 4 * N ^ (-(2 : ℝ) ^ (-(t : ℝ))) := by
  have hN0 : 0 < N := by linarith
  set L := Real.logb 2 N with hL
  have hLpos : 0 < L := Real.logb_pos (by norm_num) hN
  -- 2^t ≤ L
  have h2t : (2 : ℝ) ^ (t : ℝ) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) ht
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hLpos] at this
  have hNL : N = (2 : ℝ) ^ L := (Real.rpow_logb (by norm_num) (by norm_num) hN0).symm
  -- the main induction
  have key : ∀ s : ℕ, s ≤ t →
      0 ≤ fIter s (1 / N) ∧ fIter s (1 / N) ≤ 4 * N ^ (-(2 : ℝ) ^ (-(s : ℝ))) := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [fIter, Function.iterate_zero, id, CharP.cast_eq_zero, neg_zero,
        Real.rpow_zero, Real.rpow_neg_one]
      refine ⟨by positivity, ?_⟩
      rw [one_div]
      have : 0 < N⁻¹ := by positivity
      linarith
    | succ s ih =>
      intro hs
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hfs : fIter (s + 1) (1 / N) = fStep (fIter s (1 / N)) := by
        simp only [fIter, Function.iterate_succ_apply']
      rw [hfs]
      refine ⟨fStep_nonneg h0, ?_⟩
      set c : ℝ := (2 : ℝ) ^ (-((s + 1 : ℕ) : ℝ)) with hc
      set b : ℝ := N ^ (-c) with hb
      have hb0 : 0 ≤ b := Real.rpow_nonneg hN0.le _
      -- b^2 = a
      have hsq : b ^ 2 = N ^ (-(2 : ℝ) ^ (-(s : ℝ))) := by
        rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        rw [hc]
        push_cast
        have : (2 : ℝ) ^ (-((s : ℝ) + 1)) * 2 = (2 : ℝ) ^ (-(s : ℝ)) := by
          rw [show -((s : ℝ) + 1) = -(s : ℝ) - 1 by ring,
            Real.rpow_sub (by norm_num), Real.rpow_one]
          field_simp
        linarith
      -- b ≤ 1/2
      have hbhalf : b ≤ 1 / 2 := by
        have hcL : 1 ≤ c * L := by
          have hs' : ((s + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hs
          have h1 : (2 : ℝ) ^ ((s + 1 : ℕ) : ℝ) ≤ L :=
            le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hs') h2t
          have hpos : 0 < (2 : ℝ) ^ ((s + 1 : ℕ) : ℝ) := by positivity
          rw [hc, Real.rpow_neg (by norm_num)]
          rw [← div_eq_inv_mul, le_div_iff₀ hpos]
          linarith
        have hNc : 2 ≤ N ^ c := by
          rw [hNL, ← Real.rpow_mul (by norm_num), mul_comm]
          calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ 2 ^ (c * L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hcL
        rw [hb, Real.rpow_neg hN0.le, one_div]
        exact inv_anti₀ (by norm_num) hNc
      have hstep : fStep (fIter s (1 / N)) ≤ fStep (4 * b ^ 2) := by
        rw [hsq]; exact fStep_mono h1
      have hval : fStep (4 * b ^ 2) = 4 * b ^ 2 + 2 * b := by
        unfold fStep
        rw [show (4 : ℝ) * b ^ 2 = (2 * b) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      rw [hval] at hstep
      have : 4 * b ^ 2 + 2 * b ≤ 4 * b := by nlinarith
      linarith
  exact (key t le_rfl).2
