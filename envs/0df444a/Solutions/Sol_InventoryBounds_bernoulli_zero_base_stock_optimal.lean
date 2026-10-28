-- Prove2me | solution 1 for InventoryBounds.bernoulli_zero_base_stock_optimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:11:27.082055+00:00
-- url     : https://prove2.me/submissions/06686187-ffaf-468d-b212-1682d2b648f3

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open InventoryBounds

namespace S214IB

lemma cost_mono (ρ m y : ℝ) (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) (hm : 0 ≤ m) (hmy : m ≤ y) :
    ρ * stageCost 1 1 m 0 + (1 - ρ) * stageCost 1 1 m 1 ≤
      ρ * stageCost 1 1 y 0 + (1 - ρ) * stageCost 1 1 y 1 := by
  unfold stageCost
  have h0m : max (m - 0) 0 = m := by rw [sub_zero]; exact max_eq_left hm
  have h0y : max (y - 0) 0 = y := by rw [sub_zero]; exact max_eq_left (hm.trans hmy)
  have h1m : max (0 - m) 0 = 0 := max_eq_right (by linarith)
  have h1y : max (0 - y) 0 = 0 := max_eq_right (by linarith)
  rw [h0m, h0y, h1m, h1y]
  have key : max (m - 1) 0 + max (1 - m) 0 ≤ max (y - 1) 0 + max (1 - y) 0 + (y - m) := by
    rcases le_total m 1 with h | h <;> rcases le_total y 1 with h' | h' <;>
      simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, h, h'] <;> linarith
  nlinarith

lemma step_mono (n : ℕ) (ρ m y : ℝ) (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) (hm : 0 ≤ m) (hmy : m ≤ y)
    (hZ : Monotone (zeroBaseStockValue n ρ)) :
    ρ * (stageCost 1 1 m 0 + zeroBaseStockValue n ρ m) +
        (1 - ρ) * (stageCost 1 1 m 1 + zeroBaseStockValue n ρ (m - 1)) ≤
      ρ * (stageCost 1 1 y 0 + zeroBaseStockValue n ρ y) +
        (1 - ρ) * (stageCost 1 1 y 1 + zeroBaseStockValue n ρ (y - 1)) := by
  have h1 := cost_mono ρ m y hρ hρ1 hm hmy
  have h2 := hZ hmy
  have h3 := hZ (by linarith : m - 1 ≤ y - 1)
  have hρ0 : 0 ≤ 1 - ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ ρ),
    mul_le_mul_of_nonneg_left h3 hρ0]

lemma main (ρ : ℝ) (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) (n : ℕ) :
    bernoulliDP n ρ = zeroBaseStockValue n ρ ∧ Monotone (zeroBaseStockValue n ρ) := by
  induction n with
  | zero =>
    refine ⟨funext fun x => ?_, fun a b _ => ?_⟩ <;> simp [bernoulliDP, zeroBaseStockValue]
  | succ n ih =>
    obtain ⟨hB, hZ⟩ := ih
    have hEq : ∀ x, zeroBaseStockValue (n + 1) ρ x =
        ρ * (stageCost 1 1 (max x 0) 0 + zeroBaseStockValue n ρ (max x 0)) +
        (1 - ρ) * (stageCost 1 1 (max x 0) 1 + zeroBaseStockValue n ρ (max x 0 - 1)) := by
      intro x; rfl
    refine ⟨funext fun x => ?_, fun a b hab => ?_⟩
    · show sInf _ = _
      rw [hB, hEq]
      refine IsLeast.csInf_eq ⟨⟨max x 0, Set.mem_Ici.mpr le_rfl, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact step_mono n ρ _ y hρ hρ1 (le_max_right _ _) hy hZ
    · rw [hEq, hEq]
      exact step_mono n ρ _ _ hρ hρ1 (le_max_right _ _) (max_le_max hab le_rfl) hZ

end S214IB

theorem solution (T : ℕ) (ρ x : ℝ)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ x = zeroBaseStockValue T ρ x := by
  rw [(S214IB.main ρ hρ hρ1 T).1]
