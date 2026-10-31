-- Prove2me | solution 1 for LeaderStyle.WageFloor.cost_F
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:06:57.580955+00:00
-- url     : https://prove2.me/submissions/9039f877-3727-47dd-bde8-85033403ab48

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .F x})
      (P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have hρb : P.rho * (P.c / P.rho - P.r) = P.c - P.rho * P.r := by field_simp; try ring
  have hm1 := le_max_left P.ur P.wf
  have hm2 := le_max_right P.ur P.wf
  constructor
  · refine ⟨⟨max P.ur P.wf, P.c / P.rho - P.r, P.ul + leaderCost P .F⟩, ?_, ?_⟩
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hρb, hm1, hm2]
    · simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible]
      linear_combination hρb
  · rintro _ ⟨⟨w, b, wl⟩, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [utilLow, utilHigh, leaderCost, Style.onHigh, Style.onLow, actionValue, costHigh, costLow, cost, Feasible] at h1 h2 h3 h4 ⊢
    have hm : max P.ur P.wf ≤ w + P.rho * b - (P.c - P.rho * P.r) := max_le (by nlinarith) (by nlinarith)
    nlinarith [hm]
