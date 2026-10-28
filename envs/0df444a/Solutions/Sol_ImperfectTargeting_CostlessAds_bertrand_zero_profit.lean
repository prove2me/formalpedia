-- Prove2me | solution 1 for ImperfectTargeting.CostlessAds.bertrand_zero_profit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:00:00.206611+00:00
-- url     : https://prove2.me/submissions/40f9c365-16f0-41c9-92ae-70c03a9ada64

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

open ImperfectTargeting.CostlessAds in
theorem solution (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    IsPricingNE A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) ∧
    U₁ A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) = 0 ∧
    U₂ A α ((.b, .all), (.b, .all)) (Measure.dirac 0) (Measure.dirac 0) = 0 := by
  have hsh : shoppers α ((.b, .all), (.b, .all)) = 1 := by
    simp [shoppers, reach]
  have hl1 : loyal₁ α ((.b, .all), (.b, .all)) = 0 := by
    simp [loyal₁, hsh, reach]
  have hl2 : loyal₂ α ((.b, .all), (.b, .all)) = 0 := by
    simp [loyal₂, hsh, reach]
  have hv : val A Group.b = 1 := rfl
  have hp00 : profit 1 0 1 0 0 = 0 := by simp [profit]
  have hdev : ∀ p' : ℝ, profit 1 0 1 p' 0 ≤ 0 := by
    intro p'
    unfold profit
    split_ifs with h1 h2 h3 <;> nlinarith
  have hstrat : IsStrategy (Measure.dirac (0 : ℝ)) := by
    refine ⟨inferInstance, ?_⟩
    rw [Measure.dirac_apply' _ (measurableSet_Icc).compl]
    simp
  have hE : expProfit 1 0 1 (Measure.dirac 0) (Measure.dirac 0) = 0 := by
    unfold expProfit
    rw [integral_dirac, integral_dirac, hp00]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsPricingNE IsClearinghouseNE
    simp only [hsh, hl1, hl2, hv]
    refine ⟨hstrat, hstrat, ?_, ?_⟩
    · intro p'
      rw [hE, integral_dirac]
      exact hdev p'
    · intro q'
      rw [hE, integral_dirac]
      exact hdev q'
  · unfold U₁
    simp only [hsh, hl1, hv]
    exact hE
  · unfold U₂
    simp only [hsh, hl2, hv]
    exact hE
