-- Prove2me | solution 1 for ImperfectTargeting.CostlessAds.segmentation_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:45:25.242582+00:00
-- url     : https://prove2.me/submissions/b7316080-d536-45ad-98af-8fdde8403d80

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory

open ImperfectTargeting.CostlessAds in
theorem solution (A α : ℝ) (hA0 : 0 < A) (hA1 : A < 1)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    ∀ s₁ s₂ : Scope,
      IsPricingNE A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) ∧
      U₁ A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) = reach α s₁ * A ∧
      U₂ A α ((.a, s₁), (.b, s₂)) (Measure.dirac A) (Measure.dirac 1) = reach α s₂ := by
  intro s₁ s₂
  have hpr : ∀ v L p q : ℝ, profit v L 0 p q = if v < p then 0 else p * L := by
    intro v L p q
    simp [profit]
  have hsh : shoppers α ((.a, s₁), (.b, s₂)) = 0 := by
    simp [shoppers]
  have hl1 : loyal₁ α ((.a, s₁), (.b, s₂)) = reach α s₁ := by
    simp [loyal₁, hsh]
  have hl2 : loyal₂ α ((.a, s₁), (.b, s₂)) = reach α s₂ := by
    simp [loyal₂, hsh]
  have hr : ∀ s, 0 ≤ reach α s := by
    intro s; cases s <;> simp [reach] <;> linarith
  have hva : val A Group.a = A := rfl
  have hvb : val A Group.b = 1 := rfl
  have hstrat : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → IsStrategy (Measure.dirac c) := by
    intro c h0 h1
    refine ⟨inferInstance, ?_⟩
    rw [Measure.dirac_apply' _ (measurableSet_Icc).compl]
    simp [h0, h1]
  have hE1 : expProfit A (reach α s₁) 0 (Measure.dirac A) (Measure.dirac 1) = A * reach α s₁ := by
    unfold expProfit
    rw [integral_dirac, integral_dirac, hpr, if_neg (lt_irrefl A)]
  have hE2 : expProfit 1 (reach α s₂) 0 (Measure.dirac 1) (Measure.dirac A) = reach α s₂ := by
    unfold expProfit
    rw [integral_dirac, integral_dirac, hpr, if_neg (lt_irrefl 1), one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsPricingNE IsClearinghouseNE
    simp only [hsh, hl1, hl2, hva, hvb]
    refine ⟨hstrat A hA0.le hA1.le, hstrat 1 zero_le_one le_rfl, ?_, ?_⟩
    · intro p'
      rw [hE1, integral_dirac, hpr]
      split_ifs with h
      · exact mul_nonneg hA0.le (hr s₁)
      · push_neg at h
        exact mul_le_mul_of_nonneg_right h (hr s₁)
    · intro q'
      rw [hE2, integral_dirac, hpr]
      split_ifs with h
      · exact hr s₂
      · push_neg at h
        calc q' * reach α s₂ ≤ 1 * reach α s₂ := mul_le_mul_of_nonneg_right h (hr s₂)
          _ = reach α s₂ := one_mul _
  · unfold U₁
    simp only [hsh, hl1, hva]
    rw [hE1, mul_comm]
  · unfold U₂
    simp only [hsh, hl2, hvb]
    exact hE2
