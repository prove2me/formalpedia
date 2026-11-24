-- Prove2me | solution 1 for GlobalTheory.rank_le_of_growth_in_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:38.121862+00:00
-- url     : https://prove2.me/submissions/fee5b134-9a4e-4e75-ac42-03600a8c83d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeOfGrowthInRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  intro D f α γ ρ t₀ t₁ hρ hlim hbd
  have hev : ∀ᶠ m : ℕ in atTop, ρ * (m : ℝ) ^ D * Real.exp (-(m : ℝ)) ≤ 1 := by
    have h1 : Tendsto (fun x : ℝ => x ^ D * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero D
    have h2 : Tendsto (fun m : ℕ => ρ * ((m : ℝ) ^ D * Real.exp (-(m : ℝ)))) atTop (𝓝 (ρ * 0)) :=
      (h1.comp tendsto_natCast_atTop_atTop).const_mul ρ
    rw [mul_zero] at h2
    filter_upwards [h2.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with m hm
    rw [mul_assoc]; exact hm.le
  have key : ∀ t, max t₀ (t₁ + 2) ≤ t → ρ * (t - t₁ - 2) ≤ α + γ * t := by
    intro t ht
    have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : t₁ + 2 ≤ t := le_trans (le_max_right _ _) ht
    refine ge_of_tendsto (hlim t ht0) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    set x := Real.exp ((t - t₁ - 1) * m) with hx
    have hx2 : 2 ≤ x := by
      have : 1 ≤ (t - t₁ - 1) * m := by nlinarith
      have h := Real.add_one_le_exp ((t - t₁ - 1) * m)
      linarith
    set Q := ⌊x⌋₊ with hQ
    have hQle : (Q : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hQgt : x < Q + 1 := Nat.lt_floor_add_one x
    have hQpos : 0 < Q := by
      rw [hQ]; exact Nat.floor_pos.mpr (by linarith)
    have e2 : Real.exp (-(m:ℝ)) ≤ 1 / 2 := by
      have h := Real.add_one_le_exp (m:ℝ)
      have hp : Real.exp (-(m:ℝ)) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(m:ℝ))]
    have hQge : Real.exp ((t - t₁ - 2) * m) ≤ Q := by
      have e1 : Real.exp ((t - t₁ - 2) * m) = x * Real.exp (-(m:ℝ)) := by
        rw [hx, ← Real.exp_add]; congr 1; ring
      rw [e1]
      have : x * Real.exp (-(m:ℝ)) ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left e2 (by linarith)
      linarith
    have e3 : x * Real.exp (t₁ * m) = Real.exp (-(m:ℝ)) * Real.exp (t * m) := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hρm : 0 ≤ ρ * (m : ℝ) ^ D := mul_nonneg hρ (pow_nonneg hmpos.le _)
    have hcond : ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) := by
      calc ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m)
          ≤ ρ * (m : ℝ) ^ D * x * Real.exp (t₁ * m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hρm) (Real.exp_pos _).le
        _ = (ρ * (m : ℝ) ^ D * Real.exp (-(m:ℝ))) * Real.exp (t * m) := by
            rw [mul_assoc (ρ * (m : ℝ) ^ D) x, e3]; ring
        _ ≤ 1 * Real.exp (t * m) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (t * m) := one_mul _
    have hb := hbd t m Q (by omega) hQpos hcond
    have hlog : (t - t₁ - 2) * (m : ℝ) ≤ Real.log Q :=
      calc (t - t₁ - 2) * (m : ℝ) = Real.log (Real.exp ((t - t₁ - 2) * m)) := (Real.log_exp _).symm
        _ ≤ Real.log Q := Real.log_le_log (Real.exp_pos _) hQge
    rw [le_div_iff₀ (by positivity)]
    calc ρ * (t - t₁ - 2) * (m : ℝ) ^ (D + 1) = ρ * (m : ℝ) ^ D * ((t - t₁ - 2) * m) := by ring
      _ ≤ ρ * (m : ℝ) ^ D * Real.log Q := mul_le_mul_of_nonneg_left hlog hρm
      _ ≤ f t m := hb
  by_contra h
  push_neg at h
  have hd : 0 < ρ - γ := sub_pos.mpr h
  set T := max (max t₀ (t₁ + 2)) ((α + ρ * (t₁ + 2)) / (ρ - γ) + 1) with hTdef
  have hk := key T (le_max_left _ _)
  have hT : (α + ρ * (t₁ + 2)) / (ρ - γ) + 1 ≤ T := le_max_right _ _
  have hlt : (α + ρ * (t₁ + 2)) / (ρ - γ) < T := by linarith
  have h3 : α + ρ * (t₁ + 2) < T * (ρ - γ) := (div_lt_iff₀ hd).mp hlt
  nlinarith
end GlobalTheory
