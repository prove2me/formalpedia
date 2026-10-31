-- Prove2me | solution 1 for LeaderStyle.WageFloor.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:21:27.605441+00:00
-- url     : https://prove2.me/submissions/94c48f3d-4163-4030-a0b9-82a134695cf6

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    ((Prefers P .FU .none ∧ Prefers P .FU .U ∧ Prefers P .FU .F) ↔
      (condF P ∧ condU P)) ∧
      (condF P ∧ condU P → P.ur < P.wf) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have q1 : 0 < (1 - P.rho) * P.s := mul_pos (by linarith) hs; have q2 : 0 < P.rho * P.s := mul_pos hρ hs; have q3 : 0 < (1 - P.rho) * P.kUl := mul_pos (by linarith) hkUl; have q4 : 0 < P.rho * P.kFh := mul_pos hρ hkFh; have q5 : 0 < P.rho * P.r := mul_pos hρ hr
  have pref : ∀ (A B : Style) (xA xB : Contract) (mA mB : ℝ), Feasible P A xA → cost P xA = mA →
      (∀ y, Feasible P A y → mA ≤ cost P y) → Feasible P B xB → cost P xB = mB →
      (∀ y, Feasible P B y → mB ≤ cost P y) → (Prefers P A B ↔ mA < mB) := by
    intro A B xA xB mA mB hfA hcA hlA hfB hcB hlB
    constructor
    · rintro ⟨x, hx, hlt⟩; have := hlA x hx; have := hlt xB hfB; linarith
    · intro h; exact ⟨xA, hfA, fun y hy => by have := hlB y hy; linarith⟩
  have sFU : (∃ x, Feasible P .FU x ∧ cost P x = max (P.ur + P.s) P.wf + P.c - P.rho * (P.s + P.r) + P.rho * P.kFh + (1 - P.rho) * P.kUl + P.ul) ∧ ∀ y, Feasible P .FU y → max (P.ur + P.s) P.wf + P.c - P.rho * (P.s + P.r) + P.rho * P.kFh + (1 - P.rho) * P.kUl + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho - P.r - P.s) = P.c - P.rho * P.r - P.rho * P.s := by field_simp; try ring
    have hm1 := le_max_left (P.ur + P.s) P.wf
    have hm2 := le_max_right (P.ur + P.s) P.wf
    constructor
    · refine ⟨⟨max (P.ur + P.s) P.wf, P.c / P.rho - P.r - P.s, P.ul + leaderCost P .FU⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | linarith [hρb, hm1, hm2] | nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max (P.ur + P.s) P.wf ≤ w + P.rho * b - (P.c - P.rho * P.r - P.rho * P.s) := max_le (by linarith) (by linarith)
      linarith [hm]
  obtain ⟨⟨xFU, hfFU, hcFU⟩, hlFU⟩ := sFU
  have snone : (∃ x, Feasible P .none x ∧ cost P x = P.c + max P.ur P.wf + P.ul) ∧ ∀ y, Feasible P .none y → P.c + max P.ur P.wf + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho) = P.c := by field_simp; try ring
    have hm1 := le_max_left P.ur P.wf
    have hm2 := le_max_right P.ur P.wf
    constructor
    · refine ⟨⟨max P.ur P.wf, P.c / P.rho, P.ul + leaderCost P .none⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | linarith [hρb, hm1, hm2] | nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max P.ur P.wf ≤ w + P.rho * b - (P.c) := max_le (by linarith) (by linarith)
      linarith [hm]
  obtain ⟨⟨xnone, hfnone, hcnone⟩, hlnone⟩ := snone
  have sU : (∃ x, Feasible P .U x ∧ cost P x = max (P.ur + P.s) P.wf + P.c - P.rho * P.s + (1 - P.rho) * P.kUl + P.ul) ∧ ∀ y, Feasible P .U y → max (P.ur + P.s) P.wf + P.c - P.rho * P.s + (1 - P.rho) * P.kUl + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho - P.s) = P.c - P.rho * P.s := by field_simp; try ring
    have hm1 := le_max_left (P.ur + P.s) P.wf
    have hm2 := le_max_right (P.ur + P.s) P.wf
    constructor
    · refine ⟨⟨max (P.ur + P.s) P.wf, P.c / P.rho - P.s, P.ul + leaderCost P .U⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | linarith [hρb, hm1, hm2] | nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max (P.ur + P.s) P.wf ≤ w + P.rho * b - (P.c - P.rho * P.s) := max_le (by linarith) (by linarith)
      linarith [hm]
  obtain ⟨⟨xU, hfU, hcU⟩, hlU⟩ := sU
  have sF : (∃ x, Feasible P .F x ∧ cost P x = P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul) ∧ ∀ y, Feasible P .F y → P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho - P.r) = P.c - P.rho * P.r := by field_simp; try ring
    have hm1 := le_max_left P.ur P.wf
    have hm2 := le_max_right P.ur P.wf
    constructor
    · refine ⟨⟨max P.ur P.wf, P.c / P.rho - P.r, P.ul + leaderCost P .F⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | linarith [hρb, hm1, hm2] | nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max P.ur P.wf ≤ w + P.rho * b - (P.c - P.rho * P.r) := max_le (by linarith) (by linarith)
      linarith [hm]
  obtain ⟨⟨xF, hfF, hcF⟩, hlF⟩ := sF
  rw [pref .FU .none xFU xnone _ _ hfFU hcFU hlFU hfnone hcnone hlnone, pref .FU .U xFU xU _ _ hfFU hcFU hlFU hfU hcU hlU, pref .FU .F xFU xF _ _ hfFU hcFU hlFU hfF hcF hlF]
  clear pref hfFU hcFU hlFU xFU hfnone hcnone hlnone xnone hfU hcU hlU xU hfF hcF hlF xF
  unfold condF condU
  constructor
  · simp only [max_def, min_def]; split_ifs <;> constructor <;> intro h <;> (try obtain ⟨h1, h2, h3⟩ := h) <;> (try obtain ⟨h1, h2⟩ := h) <;> (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> first | linarith | nlinarith
  · rintro ⟨h1, h2⟩; simp only [max_def] at h2; split_ifs at h2 <;> first | linarith | nlinarith
