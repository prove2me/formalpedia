-- Prove2me | solution 1 for LeaderStyle.WageFloor.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:10:36.018768+00:00
-- url     : https://prove2.me/submissions/97a51870-5675-4b5a-9d9b-a1ec2565575b

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    Prefers P .F .none ↔ condF P := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have pref : ∀ (A B : Style) (xA xB : Contract) (mA mB : ℝ), Feasible P A xA → cost P xA = mA →
      (∀ y, Feasible P A y → mA ≤ cost P y) → Feasible P B xB → cost P xB = mB →
      (∀ y, Feasible P B y → mB ≤ cost P y) → (Prefers P A B ↔ mA < mB) := by
    intro A B xA xB mA mB hfA hcA hlA hfB hcB hlB
    constructor
    · rintro ⟨x, hx, hlt⟩; have := hlA x hx; have := hlt xB hfB; linarith
    · intro h; exact ⟨xA, hfA, fun y hy => by have := hlB y hy; linarith⟩
  have sF : (∃ x, Feasible P .F x ∧ cost P x = P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul) ∧ ∀ y, Feasible P .F y → P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul ≤ cost P y := by
    have hρb : P.rho * (P.c / P.rho - P.r) = P.c - P.rho * P.r := by field_simp; try ring
    have hm1 := le_max_left P.ur P.wf
    have hm2 := le_max_right P.ur P.wf
    constructor
    · refine ⟨⟨max P.ur P.wf, P.c / P.rho - P.r, P.ul + leaderCost P .F⟩, ?_, ?_⟩
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
      · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
        linear_combination hρb
    · rintro ⟨w, b, wl⟩ ⟨h1, h2, h3, h4⟩
      simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
      have hm : max P.ur P.wf ≤ w + P.rho * b - (P.c - P.rho * P.r) := max_le (by nlinarith) (by nlinarith)
      nlinarith [hm]
  obtain ⟨⟨xF, hfF, hcF⟩, hlF⟩ := sF
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
  rw [pref .F .none xF xnone _ _ hfF hcF hlF hfnone hcnone hlnone]; unfold condF; simp only [max_def, min_def]; split_ifs <;> constructor <;> intro h <;> nlinarith
