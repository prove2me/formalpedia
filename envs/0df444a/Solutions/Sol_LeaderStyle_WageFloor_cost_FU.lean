-- Prove2me | solution 1 for LeaderStyle.WageFloor.cost_FU
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:09:06.940388+00:00
-- url     : https://prove2.me/submissions/d93bb5fc-7265-403f-87d6-aa954ab29528

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .FU x})
      (max (P.ur + P.s) P.wf + P.c - P.rho * (P.s + P.r) +
        P.rho * P.kFh + (1 - P.rho) * P.kUl + P.ul) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have hρb : P.rho * (P.c / P.rho - P.r - P.s) = P.c - P.rho * P.r - P.rho * P.s := by field_simp; try ring
  have hm1 := le_max_left (P.ur + P.s) P.wf
  have hm2 := le_max_right (P.ur + P.s) P.wf
  constructor
  · refine ⟨⟨max (P.ur + P.s) P.wf, P.c / P.rho - P.r - P.s, P.ul + leaderCost P .FU⟩, ?_, ?_⟩
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      linear_combination hρb
  · rintro _ ⟨⟨w, b, wl⟩, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
    have hm : max (P.ur + P.s) P.wf ≤ w + P.rho * b - (P.c - P.rho * P.r - P.rho * P.s) := max_le (by nlinarith) (by nlinarith)
    nlinarith [hm]
