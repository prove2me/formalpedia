-- Prove2me | solution 1 for MajorityAttack.NegCost.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:38:10.526385+00:00
-- url     : https://prove2.me/submissions/7e3724ab-0a94-4377-aee8-1ae4665440a8

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

open MajorityAttack.NegCost

theorem solution (τ H L ρ ρt : ℝ) (c : ℝ → ℝ) (htil : ℝ)
    (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L) (hreward : ρ < ρt)
    (hc : CostStanding c) (hopt : IsAttackOptimum (τ * H) ρt c htil) :
    ∃ hhat : ℝ, 0 < hhat ∧ hhat < H / 2 ∧
      ∀ hstar : ℝ, hhat ≤ hstar → MajorityAttack.NegCost.netCost τ H L ρ ρt c htil hstar < 0 := by
  obtain ⟨hpos, hmax⟩ := hopt
  have hDpos : 0 < τ * H := mul_pos hτ hH
  -- the attack-chain profit is nonincreasing to the right of its maximiser
  have hanti : ∀ x y : ℝ, htil ≤ x → x ≤ y →
      flowProfit (τ * H) ρt c y ≤ flowProfit (τ * H) ρt c x := by
    intro x y hx hxy
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    have hy : htil < y := lt_of_le_of_lt hx h
    have hyh : 0 < y - htil := by linarith
    set t := (y - x) / (y - htil) with ht
    set s := (x - htil) / (y - htil) with hs
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hyh.le
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hyh.le
    have hts : t + s = 1 := by
      rw [ht, hs, ← add_div]; field_simp; ring
    have hcomb : t * htil + s * y = x := by
      rw [ht, hs]; field_simp; ring
    have hconv := hc.convex.2 (Set.mem_Ici.2 hpos) (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ y))
      ht0 hs0 hts
    simp only [smul_eq_mul] at hconv
    rw [hcomb] at hconv
    have hmy : flowProfit (τ * H) ρt c y ≤ flowProfit (τ * H) ρt c htil :=
      hmax (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ y))
    have key : x / (τ * H) * ρt = t * (htil / (τ * H) * ρt) + s * (y / (τ * H) * ρt) := by
      rw [← hcomb]; ring
    have hm := mul_le_mul_of_nonneg_left hmy ht0
    unfold flowProfit at hmy hm ⊢
    have hs' : s = 1 - t := by linarith
    rw [hs'] at key hconv
    nlinarith
  -- continuity of the cost at H/2
  have hcont : ContinuousAt c (H / 2) := by
    have := hc.convex.continuousOn_interior
    rw [interior_Ici] at this
    exact this.continuousAt (Ioi_mem_nhds (by linarith))
  let g : ℝ → ℝ := fun h => flowProfit (τ * H) ρt c (H - h) - flowProfit (τ * H) ρ c h
  have hgc : ContinuousAt g (H / 2) := by
    have h1 : ContinuousAt (fun h => c (H - h)) (H / 2) := by
      have e : H - H / 2 = H / 2 := by ring
      have hc' : ContinuousAt c (H - H / 2) := by rw [e]; exact hcont
      exact ContinuousAt.comp (f := fun h => H - h) hc' (by fun_prop)
    have h2 : ContinuousAt (fun h : ℝ => (H - h) / (τ * H) * ρt) (H / 2) := by fun_prop
    have h3 : ContinuousAt (fun h : ℝ => h / (τ * H) * ρ) (H / 2) := by fun_prop
    exact (h2.sub h1).sub (h3.sub hcont)
  have hg0 : 0 < g (H / 2) := by
    have e : H - H / 2 = H / 2 := by ring
    simp only [g, flowProfit, e]
    have : 0 < H / 2 / (τ * H) * (ρt - ρ) := mul_pos (div_pos (by linarith) hDpos) (by linarith)
    nlinarith
  have hev := hgc.eventually (lt_mem_nhds hg0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨max (H / 4) (H / 2 - δ / 2), lt_max_of_lt_left (by linarith),
    max_lt (by linarith) (by linarith), ?_⟩
  intro hstar hle
  have hst : 0 < hstar := lt_of_lt_of_le (lt_max_of_lt_left (by linarith)) hle
  have hstar2 : H / 2 - δ / 2 ≤ hstar := le_trans (le_max_right _ _) hle
  unfold netCost
  apply mul_neg_of_neg_of_pos _ hL
  rw [sub_neg]
  have hstrict : flowProfit (τ * H) ρ c hstar < flowProfit (τ * H) ρt c hstar := by
    unfold flowProfit
    have : 0 < hstar / (τ * H) * (ρt - ρ) := mul_pos (div_pos hst hDpos) (by linarith)
    nlinarith
  have hmaxs : flowProfit (τ * H) ρt c hstar ≤ flowProfit (τ * H) ρt c htil :=
    hmax (Set.mem_Ici.2 hst.le)
  by_cases hA : minAttackPower H hstar ≤ htil
  · rw [max_eq_left hA]; linarith
  · rw [not_le] at hA
    rw [max_eq_right hA.le]
    by_cases hs : H / 2 ≤ hstar
    · have hm : minAttackPower H hstar = H / 2 := by
        unfold minAttackPower; apply max_eq_left; linarith
      rw [hm] at hA ⊢
      have := hanti (H / 2) hstar hA.le hs
      linarith
    · rw [not_le] at hs
      have hm : minAttackPower H hstar = H - hstar := by
        unfold minAttackPower; apply max_eq_right; linarith
      rw [hm]
      have hd : dist hstar (H / 2) < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have := hball hd
      simp only [g] at this
      linarith
