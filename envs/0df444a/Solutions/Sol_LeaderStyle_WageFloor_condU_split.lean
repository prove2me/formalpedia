-- Prove2me | solution 1 for LeaderStyle.WageFloor.condU_split
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:23:29.442785+00:00
-- url     : https://prove2.me/submissions/ef042064-1340-4bf9-a024-52b963e2808d

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model
open LeaderStyle.WageFloor

theorem solution(P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    condU P ↔ P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have q1 : 0 < (1 - P.rho) * P.s := mul_pos (by linarith) hs
  have q2 : 0 < P.rho * P.s := mul_pos hρ hs
  have q3 : 0 < (1 - P.rho) * P.kUl := mul_pos (by linarith) hkUl
  have e : P.kUl / P.s < P.rho / (1 - P.rho) ↔ (1 - P.rho) * P.kUl < P.rho * P.s := by
    rw [div_lt_div_iff₀ hs (by linarith)]; constructor <;> intro h <;> linarith
  rw [e]
  unfold condU condU'
  simp only [max_def]
  split_ifs <;> constructor <;> intro h <;> (try obtain ⟨h1, h2⟩ := h) <;> (try refine ⟨?_, ?_⟩) <;> first | linarith | nlinarith
