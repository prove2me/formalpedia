-- Prove2me | solution 1 for NonExclEncroach.Channels.proposition_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:21:06.436612+00:00
-- url     : https://prove2.me/submissions/7762a375-b213-4f6b-b901-4026e2476e9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model
import Theorems.Thm_NonExclEncroach_Channels_num1_sign
import Theorems.Thm_NonExclEncroach_Channels_lemma_4_direct_only
import Theorems.Thm_NonExclEncroach_Channels_lemma_4_reseller_and_direct

open NonExclEncroach.Channels

/-- `c0 < 0` on `(0,1)`. -/
lemma p5_c0_neg (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) : c0 θ < 0 := by
  unfold c0
  have a : θ ^ 2 < 1 := by nlinarith
  have b : θ ^ 3 < 1 := by nlinarith
  have hn : 0 < (2 - θ) * (8 - θ ^ 2 - θ ^ 3) := mul_pos (by linarith) (by linarith)
  have hd : 0 < 2 * (8 - 5 * θ ^ 2) := by linarith
  rw [neg_div]
  exact neg_neg_of_pos (div_pos hn hd)

/-- `c3 > 1/3` on `(0,1)`. -/
lemma p5_c3_gt (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) : 1 / 3 < c3 θ := by
  unfold c3
  have a2 : θ ^ 2 < 1 := by nlinarith
  have a3 : θ ^ 3 < 1 := by nlinarith
  have a4 : θ ^ 4 < 1 := by nlinarith
  have a6 : θ ^ 6 < 1 := by nlinarith
  have p2 : 0 < θ ^ 2 := by positivity
  have p4 : 0 < θ ^ 4 := by positivity
  have p5 : 0 < θ ^ 5 := by positivity
  have p6 : 0 < θ ^ 6 := by positivity
  have p7 : 0 < θ ^ 7 := by positivity
  have p8 : 0 < θ ^ 8 := by positivity
  have hd : 0 < 2 * (320 - 36 * θ ^ 2 - 42 * θ ^ 4 + θ ^ 6) := by linarith
  rw [lt_div_iff₀ hd]
  linarith

/-- `c2 < 1/5` on `(0,1)`. -/
lemma p5_c2_lt (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) : c2 θ < 1 / 5 := by
  unfold c2
  have a2 : θ ^ 2 < 1 := by nlinarith
  have a4 : θ ^ 4 < 1 := by nlinarith
  have a6 : θ ^ 6 ≤ θ ^ 2 := pow_le_pow_of_le_one h0.le h1.le (by norm_num)
  have p2 : 0 < θ ^ 2 := by positivity
  have p3 : 0 < θ ^ 3 := by positivity
  have p4 : 0 < θ ^ 4 := by positivity
  have p5 : 0 < θ ^ 5 := by positivity
  have p7 : 0 < θ ^ 7 := by positivity
  have hq : 0 < 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
  have hd : 0 < 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by positivity
  rw [div_lt_iff₀ hd]
  have e : 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) =
      2 * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) + 2 * θ * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by ring
  rw [e]
  have : 2 * θ * 99 < 2 * θ * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by
    apply mul_lt_mul_of_pos_left _ (by linarith); linarith
  nlinarith

/-- `c0 < -7/10` on `(0,1)`. -/
lemma p5_c0_lt (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) : c0 θ < -7 / 10 := by
  unfold c0
  have a2 : θ ^ 2 < 1 := by nlinarith
  have a3 : θ ^ 3 < 1 := by nlinarith
  have p4 : 0 < θ ^ 4 := by positivity
  have hd : 0 < 2 * (8 - 5 * θ ^ 2) := by linarith
  have key : 7 / 10 < (2 - θ) * (8 - θ ^ 2 - θ ^ 3) / (2 * (8 - 5 * θ ^ 2)) := by
    rw [lt_div_iff₀ hd]
    nlinarith [sq_nonneg (θ - 4 / 5)]
  rw [neg_div]
  linarith

/-- `-7/10 < c2` on `(0,1)`. -/
lemma p5_c2_gt (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) : -7 / 10 < c2 θ := by
  unfold c2
  have a2 : θ ^ 2 < 1 := by nlinarith
  have a3 : θ ^ 3 < 1 := by nlinarith
  have a4 : θ ^ 4 < 1 := by nlinarith
  have a5 : θ ^ 5 < 1 := by nlinarith
  have a7 : θ ^ 7 < 1 := by nlinarith
  have p6 : 0 < θ ^ 6 := by positivity
  have hq : 99 < 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
  have hd : 0 < 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by
    have : 0 < 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
    positivity
  rw [lt_div_iff₀ hd]
  have : 2 * 99 ≤ 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by
    have : (2 : ℝ) ≤ 2 * (1 + θ) := by linarith
    nlinarith
  nlinarith

theorem solution :
    ∃ θhat : ℝ, 0 < θhat ∧ θhat < 1 ∧ num1 θhat = 0 ∧
      (∀ θ, 0 < θ → θ < θhat →
        0 < c2 θ ∧
        ∀ c, 0 < c → c ≤ c2 θ →
          (∃ σ, IsEquilibrium θ c σ) ∧
          ∀ σ, IsEquilibrium θ c σ → σ.q1 = 0 ∧ 0 < σ.y) ∧
      (∀ θ, θhat < θ → θ < 1 → c2 θ < 0) ∧
      (∀ θ, θhat < θ → θ ≤ 9 / 10 →
        ∀ c, c2 θ < c → c < 0 →
          ∃ σ, IsEquilibrium θ c σ ∧ 0 < σ.q1 ∧ 0 < σ.y) := by
  obtain ⟨hanti, hpos, hneg, hsign⟩ := num1_sign
  have hcont : Continuous num1 := by unfold num1; fun_prop
  -- root of `num1` in `[1/10, 9/10]`
  have h9 : num1 (9 / 10) < 0 := by norm_num [num1]
  obtain ⟨θhat, ⟨hl, hu⟩, hroot⟩ :
      ∃ t ∈ Set.Icc (1 / 10 : ℝ) (9 / 10), num1 t = 0 := by
    have := intermediate_value_Icc' (show (1 / 10 : ℝ) ≤ 9 / 10 by norm_num)
      hcont.continuousOn
    exact this ⟨h9.le, hpos.le⟩
  have hmem : ∀ t, 0 ≤ t → t ≤ 1 → t ∈ Set.Icc (0 : ℝ) 1 := fun t a b => ⟨a, b⟩
  refine ⟨θhat, by linarith, by linarith, hroot, ?_, ?_, ?_⟩
  · intro θ h0 hlt
    have hn : 0 < num1 θ := by
      have := hanti (hmem θ h0.le (by linarith)) (hmem θhat (by linarith) (by linarith)) hlt
      linarith
    have hθ1 : θ < 1 := by linarith
    have hc2 : 0 < c2 θ := ((hsign θ h0 hθ1).1).2 hn
    refine ⟨hc2, ?_⟩
    intro c hc hcle
    have hS : Standing θ c :=
      ⟨h0, hθ1, lt_trans (p5_c0_neg θ h0 hθ1) hc,
        by linarith [p5_c2_lt θ h0 hθ1, p5_c3_gt θ h0 hθ1]⟩
    obtain ⟨hDO, hDOB, hall⟩ := lemma_4_direct_only θ c hS (by linarith) hcle
    refine ⟨?_, hall⟩
    rcases le_total c (c1 θ) with h | h
    · obtain ⟨σ, hσ, -, -⟩ := hDO h (max 0 (wU θ c (wDO2 θ c) (wDO2 θ c)))
        (le_max_left _ _) (le_max_right _ _)
      exact ⟨σ, hσ⟩
    · obtain ⟨σ, hσ, -, -⟩ := hDOB h
      exact ⟨σ, hσ⟩
  · intro θ hlt h1
    have h0 : 0 < θ := by linarith
    have hn : num1 θ < 0 := by
      have := hanti (hmem θhat (by linarith) (by linarith)) (hmem θ h0.le h1.le) hlt
      linarith
    exact ((hsign θ h0 h1).2).2 hn
  · intro θ hlt h9' c hc2 hc0
    have h0 : 0 < θ := by linarith
    have h1 : θ < 1 := by linarith
    have hn : num1 θ < 0 := by
      have := hanti (hmem θhat (by linarith) (by linarith)) (hmem θ h0.le h1.le) hlt
      linarith
    have hc2neg : c2 θ < 0 := ((hsign θ h0 h1).2).2 hn
    have hS : Standing θ c :=
      ⟨h0, h1, by linarith [p5_c0_lt θ h0 h1, p5_c2_gt θ h0 h1], by linarith [p5_c3_gt θ h0 h1]⟩
    obtain ⟨σ, hσ, -, -, hq, hy⟩ := lemma_4_reseller_and_direct θ c hS hc2 h9' hc0
    exact ⟨σ, hσ, hq, hy⟩
