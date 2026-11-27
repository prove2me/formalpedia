-- Prove2me | solution 1 for InnovAlloc.Optimal.Supplement.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:19.494175+00:00
-- url     : https://prove2.me/submissions/338c728a-bf2f-4d11-b376-70fc32243186

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_MonoSharing

open InnovAlloc
open InnovAlloc.Optimal
open InnovAlloc.Optimal.Supplement

/-- Proposition 4 (p. 18), all four conclusions in the actual one-agent effort game. -/
theorem solution (α B : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hB : 1 < B) :
    IsMonoShare B (gammaM B) ∧
    (∀ γ, IsMonoShare B γ → γ = gammaM B) ∧
    profitMono (gammaM B) B = monoValue B ∧
    IsEquilibrium α (gammaM B) B 0 (Real.log (Real.sqrt B) / B) 0 ∧
    ∀ x1 x2, IsEquilibrium α (gammaM B) B 0 x1 x2 →
      x1 = Real.log (Real.sqrt B) / B ∧ x2 = 0 ∧
      principalProfit α (gammaM B) B 0 x1 x2 = (1 - 1 / Real.sqrt B) ^ 2 ∧
      agentPayoff α (gammaM B) B x1 0 x2 =
        1 / Real.sqrt B - 1 / B + Real.log (1 / Real.sqrt B) / B := by
          set s := Real.sqrt B with hs_def
          have hB0 : 0 < B := by linarith
          have hs0 : 0 < s := Real.sqrt_pos.mpr hB0
          have hs1 : 1 < s := by
            rw [hs_def]; rw [show (1:ℝ) = Real.sqrt 1 by simp]
            exact Real.sqrt_lt_sqrt (by norm_num) hB
          have hss : s * s = B := Real.mul_self_sqrt hB0.le
          have hγ : gammaM B = 1 / s := rfl
          have hγB : gammaM B * B = s := by
            rw [hγ, ← hss]; field_simp
          have hpm : ∀ η, 1 < η * B → profitMono η B = (1 - η) * (1 - 1 / (η * B)) := by
            intro η h
            unfold profitMono; rw [if_neg (by linarith)]
          have hpmG : profitMono (gammaM B) B = (1 - 1 / s) ^ 2 := by
            rw [hpm _ (by rw [hγB]; exact hs1), hγB, hγ]; ring
          -- gap identity
          have hgap : ∀ η, 0 < η → (1 - 1 / s) ^ 2 - (1 - η) * (1 - 1 / (η * B)) = (η - 1/s)^2 / η := by
            intro η hη
            rw [← hss]; field_simp; ring
          have hmono : IsMonoShare B (gammaM B) := by
            refine ⟨⟨by rw [hγ]; positivity, by rw [hγ, div_lt_one hs0]; exact hs1⟩, ?_⟩
            intro η hη
            rw [hpmG]
            by_cases h : η * B ≤ 1
            · unfold profitMono; rw [if_pos h]; positivity
            · push Not at h
              rw [hpm _ h]
              have := hgap η hη.1
              have : 0 ≤ (η - 1/s)^2 / η := by have := hη.1; positivity
              linarith
          have hx : Real.exp (-(B * (Real.log s / B))) = 1 / s := by
            rw [mul_div_cancel₀ _ hB0.ne', Real.exp_neg, Real.exp_log hs0, one_div]
          set xs := Real.log s / B with hxs
          have hxs0 : 0 ≤ xs := div_nonneg (Real.log_nonneg hs1.le) hB0.le
          have hsuccxs : succ B xs = 1 - 1 / s := by unfold succ; rw [hx]
          have hsucc0 : ∀ x, succ 0 x = 0 := by intro x; unfold succ; simp
          -- key: g(y) ≤ g(xs) with equality only at xs
          have hrepr : ∀ y, gammaM B * succ B y - y
              = gammaM B - Real.exp (-(B * (y - xs))) / B - y := by
            intro y
            have : Real.exp (-(B * y)) = (1 / s) * Real.exp (-(B * (y - xs))) := by
              rw [← hx, ← Real.exp_add]; congr 1; ring
            unfold succ; rw [this, hγ, ← hss]; field_simp
          have hgxs : gammaM B * succ B xs - xs = gammaM B - 1 / B - xs := by
            rw [hrepr]; simp
          have hle : ∀ y, gammaM B * succ B y - y ≤ gammaM B * succ B xs - xs := by
            intro y
            rw [hrepr, hgxs]
            have h1 := Real.add_one_le_exp (-(B * (y - xs)))
            have : 1 / B + (xs - y) ≤ Real.exp (-(B * (y - xs))) / B := by
              rw [le_div_iff₀ hB0]
              have : (1 / B + (xs - y)) * B = 1 + B * (xs - y) := by field_simp
              rw [this]; linarith
            linarith
          have huniq : ∀ y, gammaM B * succ B xs - xs ≤ gammaM B * succ B y - y → y = xs := by
            intro y hy
            by_contra hne
            have hne' : -(B * (y - xs)) ≠ 0 := by
              intro h
              apply hne
              have : B * (y - xs) = 0 := by linarith
              rcases mul_eq_zero.mp this with h | h
              · linarith
              · linarith
            rw [hgxs, hrepr y] at hy
            have h1 := Real.add_one_lt_exp hne'
            have : 1 / B + (xs - y) < Real.exp (-(B * (y - xs))) / B := by
              rw [lt_div_iff₀ hB0]
              have : (1 / B + (xs - y)) * B = 1 + B * (xs - y) := by field_simp
              rw [this]; linarith
            linarith
          have hpay1 : ∀ z1 z2, agentPayoff α (gammaM B) B z1 0 z2 = gammaM B * succ B z1 - z1 := by
            intro z1 z2; unfold agentPayoff; rw [hsucc0]; ring
          have hpay2 : ∀ z1 z2, agentPayoff α (gammaM B) 0 z2 B z1 = - z2 := by
            intro z1 z2; unfold agentPayoff; rw [hsucc0]; ring
          refine ⟨hmono, ?_, ?_, ?_, ?_⟩
          · intro γ hγm
            have h := hγm.2 (gammaM B) hmono.1
            rw [hpmG] at h
            have hpos : 0 < (1 - 1 / s) ^ 2 := by
              have : 1 / s < 1 := by rw [div_lt_one hs0]; exact hs1
              have : 0 < 1 - 1/s := by linarith
              positivity
            have hγB1 : 1 < γ * B := by
              by_contra hc
              push Not at hc
              unfold profitMono at h; rw [if_pos hc] at h; linarith
            rw [hpm _ hγB1] at h
            have hg := hgap γ hγm.1.1
            have h0 : (γ - 1/s)^2 / γ ≤ 0 := by linarith
            have h0' : (γ - 1/s)^2 ≤ 0 := by
              have := (div_nonpos_iff.mp h0)
              rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
              · linarith [hγm.1.1]
              · exact h1
            have : γ - 1/s = 0 := by nlinarith [sq_nonneg (γ - 1/s)]
            rw [hγ]; linarith
          · rw [hpmG]; rfl
          · refine ⟨⟨xs, hxs0⟩, ⟨0, le_refl _⟩, rfl, rfl, ?_, ?_⟩
            · intro y1
              simp only
              rw [hpay1, hpay1]; exact hle _
            · intro y2
              simp only
              rw [hpay2, hpay2]; simpa using y2.2
          · intro x1 x2 heq
            obtain ⟨v1, v2, rfl, rfl, h1, h2⟩ := heq
            have hx2 : v2.1 = 0 := by
              have := h2 ⟨0, le_refl _⟩
              simp only at this
              rw [hpay2, hpay2] at this
              linarith [v2.2]
            have hx1 : v1.1 = xs := by
              have := h1 ⟨xs, hxs0⟩
              simp only at this
              rw [hpay1, hpay1] at this
              exact huniq _ this
            refine ⟨hx1, hx2, ?_, ?_⟩
            · unfold principalProfit; rw [hx1, hsucc0, hsuccxs, hγ]; ring
            · rw [hpay1, hx1, hsuccxs, hγ, one_div, Real.log_inv, hxs, ← hss]
              field_simp; ring
