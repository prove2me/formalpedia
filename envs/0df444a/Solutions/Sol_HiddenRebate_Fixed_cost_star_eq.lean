-- Prove2me | solution 1 for HiddenRebate.Fixed.cost_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:52:31.98495+00:00
-- url     : https://prove2.me/submissions/61f1745a-2653-4d80-8189-c50259e23449

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

open HiddenRebate.Fixed MeasureTheory

theorem solution (μ : Measure ℝ) (r : ℝ) (hμ : Standing μ r) :
    Integrable (costIntegrand r (contractStar r).1 (contractStar r).2) (μ.prod μ) ∧
    cost μ r (contractStar r).1 (contractStar r).2 = ∫ x, (min x.1 x.2 + r) ∂(μ.prod μ) := by
  obtain ⟨hprob, -, -, hint, -⟩ := hμ
  have hpt : costIntegrand r (contractStar r).1 (contractStar r).2 = fun x => min x.1 x.2 + r := by
    funext x
    simp only [costIntegrand, contractStar, feeStar, selStar, quote, add_sub_cancel_right]
    by_cases h : x.1 ≤ x.2
    · simp [h, sel]
    · simp [h, sel]; linarith
  have h1 : Integrable (fun x : ℝ × ℝ => x.1) (μ.prod μ) := hint.comp_fst μ
  have h2 : Integrable (fun x : ℝ × ℝ => x.2) (μ.prod μ) := hint.comp_snd μ
  refine ⟨?_, ?_⟩
  · rw [hpt]; exact (h1.inf h2).add (integrable_const r)
  · simp only [cost, hpt]
