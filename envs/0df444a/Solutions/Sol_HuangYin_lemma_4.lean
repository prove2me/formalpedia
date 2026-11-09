-- Prove2me | solution 1 for HuangYin.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:09:19.111642+00:00
-- url     : https://prove2.me/submissions/4a179c5e-2703-46e7-bf7f-503987f09fb0

import Mathlib
import Definitions.Def_HuangYin_opaqueProfit
import Definitions.Def_HuangYin_vHL

open HuangYin in
theorem solution (P : Params) :
    (∀ x1 ∈ Set.Icc (0 : ℝ) 1, ∀ x2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) x1 x2 ≤
        max (opaqueProfit P P.vL (vHL P) 0 x2) (opaqueProfit P P.vL (vHL P) 1 x2)) ∧
    (∀ x2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) 1 x2 ≤ opaqueProfit P (vHL P) (vHL P) 1 x2) ∧
    (∀ x2 ∈ Set.Icc (0 : ℝ) 1, ∃ y1 ∈ Set.Icc (0 : ℝ) 1, ∃ y2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P P.vL (vHL P) 0 x2 ≤ opaqueProfit P (vHL P) P.vL y1 y2) := by
  have hv := P.hv
  have hα0 := P.hα0
  have hα1 := P.hα1
  have hef : estimate false = 0 := by simp [estimate]
  have het : estimate true = 1 / 2 := by norm_num [estimate]
  have hvHL : vHL P = (P.vH + P.vL) / 2 := by unfold vHL; ring
  have hLf : Buys P P.vL false := by unfold Buys; rw [hef]; linarith
  have hLt : Buys P P.vL true := by unfold Buys; rw [het]; linarith
  have hHf : ¬ Buys P (vHL P) false := by unfold Buys; rw [hef, hvHL]; intro h; linarith
  have hHt : Buys P (vHL P) true := by unfold Buys; rw [het, hvHL]; linarith
  have hdL : ∀ q, demand P P.vL q = 1 := by
    intro q; unfold demand; rw [if_pos hLf, if_pos hLt]; ring
  have hdH : ∀ q, demand P (vHL P) q = q := by
    intro q; unfold demand; rw [if_neg hHf, if_pos hHt]; ring
  refine ⟨fun x1 hx1 x2 hx2 => ?_, fun x2 hx2 => ?_, fun x2 hx2 => ?_⟩
  · have hlin : opaqueProfit P P.vL (vHL P) x1 x2 =
        (1 - x1) * opaqueProfit P P.vL (vHL P) 0 x2 + x1 * opaqueProfit P P.vL (vHL P) 1 x2 := by
      unfold opaqueProfit
      simp only [hdL, hdH]
      unfold cost
      ring
    rw [hlin]
    have h1 := le_max_left (opaqueProfit P P.vL (vHL P) 0 x2) (opaqueProfit P P.vL (vHL P) 1 x2)
    have h2 := le_max_right (opaqueProfit P P.vL (vHL P) 0 x2) (opaqueProfit P P.vL (vHL P) 1 x2)
    have a1 : 0 ≤ 1 - x1 := by linarith [hx1.2]
    have a2 : 0 ≤ x1 := hx1.1
    nlinarith
  · unfold opaqueProfit
    simp only [hdL, hdH]
    unfold cost
    rw [hvHL]
    nlinarith
  · unfold opaqueProfit
    simp only [hdL, hdH]
    by_cases hs : vHL P - cost P x2 ≤ 0
    · refine ⟨0, ⟨le_refl _, zero_le_one⟩, 0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      have a1 : 0 ≤ (P.α * 0 + (1 - P.α) * x2) := by nlinarith [hx2.1]
      have := mul_nonpos_of_nonneg_of_nonpos a1 hs
      unfold cost at this ⊢
      nlinarith
    · push_neg at hs
      refine ⟨x2, hx2, 0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      have a1 : P.α * 0 + (1 - P.α) * x2 ≤ x2 := by nlinarith [hx2.1]
      have := mul_le_mul_of_nonneg_right a1 hs.le
      unfold cost at this hs ⊢
      nlinarith
