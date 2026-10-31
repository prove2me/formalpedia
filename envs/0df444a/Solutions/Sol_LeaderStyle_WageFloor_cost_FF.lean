-- Prove2me | solution 1 for LeaderStyle.WageFloor.cost_FF
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:09:05.057148+00:00
-- url     : https://prove2.me/submissions/1b9dba85-6f8e-46d5-b612-b1417f78c21b

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .FF x})
      (P.c + max (P.ur - P.r) P.wf + P.rho * P.kFh +
        (1 - P.rho) * P.kFl + P.ul) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have hρb : P.rho * (P.c / P.rho) = P.c := by field_simp; try ring
  have hm1 := le_max_left (P.ur - P.r) P.wf
  have hm2 := le_max_right (P.ur - P.r) P.wf
  constructor
  · refine ⟨⟨max (P.ur - P.r) P.wf, P.c / P.rho, P.ul + leaderCost P .FF⟩, ?_, ?_⟩
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      linear_combination hρb
  · rintro _ ⟨⟨w, b, wl⟩, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
    have hm : max (P.ur - P.r) P.wf ≤ w + P.rho * b - (P.c) := max_le (by nlinarith) (by nlinarith)
    nlinarith [hm]
