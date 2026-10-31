-- Prove2me | solution 1 for LeaderStyle.WageFloor.UU_dominated
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:17:03.981835+00:00
-- url     : https://prove2.me/submissions/eb705980-a97b-4bd2-81ef-cae179f782ad

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    Prefers P .none .UU := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have pref : ∀ (A B : Style) (xA xB : Contract) (mA mB : ℝ), Feasible P A xA → cost P xA = mA →
      (∀ y, Feasible P A y → mA ≤ cost P y) → Feasible P B xB → cost P xB = mB →
      (∀ y, Feasible P B y → mB ≤ cost P y) → (Prefers P A B ↔ mA < mB) := by
    intro A B xA xB mA mB hfA hcA hlA hfB hcB hlB
    constructor
    · rintro ⟨x, hx, hlt⟩; have := hlA x hx; have := hlt xB hfB; linarith
    · intro h; exact ⟨xA, hfA, fun y hy => by have := hlB y hy; linarith⟩
  have snone : (∃ x, Feasible P .none x ∧ cost P x = P.c + max P.ur P.wf + P.ul) ∧ ∀ y, Feasible P .none y → P.c + max P.ur P.wf + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho) = P.c := by field_simp; try ring
    have hm1 := le_max_left P.ur P.wf
    have hm2 := le_max_right P.ur P.wf
    constructor
    · refine ⟨⟨max P.ur P.wf, P.c / P.rho, P.ul + leaderCost P .none⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max P.ur P.wf ≤ w + P.rho * b - (P.c) := max_le (by nlinarith) (by nlinarith)
      nlinarith [hm]
  obtain ⟨⟨xnone, hfnone, hcnone⟩, hlnone⟩ := snone
  have sUU : (∃ x, Feasible P .UU x ∧ cost P x = max (P.ur + P.s) P.wf + P.c + P.rho * P.kUh + (1 - P.rho) * P.kUl + P.ul) ∧ ∀ y, Feasible P .UU y → max (P.ur + P.s) P.wf + P.c + P.rho * P.kUh + (1 - P.rho) * P.kUl + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho) = P.c := by field_simp; try ring
    have hm1 := le_max_left (P.ur + P.s) P.wf
    have hm2 := le_max_right (P.ur + P.s) P.wf
    constructor
    · refine ⟨⟨max (P.ur + P.s) P.wf, P.c / P.rho, P.ul + leaderCost P .UU⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max (P.ur + P.s) P.wf ≤ w + P.rho * b - (P.c) := max_le (by nlinarith) (by nlinarith)
      nlinarith [hm]
  obtain ⟨⟨xUU, hfUU, hcUU⟩, hlUU⟩ := sUU
  apply (pref .none .UU xnone xUU _ _ hfnone hcnone hlnone hfUU hcUU hlUU).2
  simp only [max_def]; split_ifs <;> nlinarith [mul_pos hρ hkFh, mul_pos (sub_pos.2 hρ1) hkUl]
