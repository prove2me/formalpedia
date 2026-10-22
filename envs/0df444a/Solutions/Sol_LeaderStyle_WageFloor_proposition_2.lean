-- Prove2me | solution 1 for LeaderStyle.WageFloor.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:57:45.049304+00:00
-- url     : https://prove2.me/submissions/284a0605-2107-44c0-a86d-8e5a1d012cb5

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

set_option autoImplicit false

namespace LeaderStyle.WageFloor.P2Aux

open LeaderStyle.WageFloor

/-- Lower bound on the cost of any feasible contract, given a candidate value `V`
dominated by every style's minimal surcharge. -/
theorem lb (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) (V : ℝ)
    (h0 : V ≤ 0) (hF : V ≤ P.rho * (P.kFh - P.r))
    (hU : V ≤ max ((1 - P.rho) * P.kUl - P.rho * P.s)
      ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur)))
    (hFU : V ≤ P.rho * (P.kFh - P.r) + max ((1 - P.rho) * P.kUl - P.rho * P.s)
      ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur)))
    (B : Style) (y : Contract) (hy : Feasible P B y) :
    P.wf + P.ul + P.c + V ≤ cost P y := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have h1ρ : 0 < 1 - P.rho := by linarith
  have p1 : 0 < P.rho * P.kFh := mul_pos hρ hkFh
  have p2 : 0 < (1 - P.rho) * P.kFl := mul_pos h1ρ (lt_of_lt_of_le hkFh hkFl)
  have p3 : 0 < P.rho * P.kUh := mul_pos hρ (lt_of_lt_of_le hkUl hkUh)
  have p4 : 0 < (1 - P.rho) * P.kUl := mul_pos h1ρ hkUl
  cases B <;>
    simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
      Style.onHigh, Style.onLow, cost] at hy ⊢ <;>
    obtain ⟨h1, h2, h3, h4⟩ := hy
  · linarith
  · linarith
  · linarith
  · have := max_le (show (1 - P.rho) * P.kUl - P.rho * P.s ≤ y.w + P.rho * y.b + y.wl - (P.wf + P.ul + P.c) by linarith)
      (show (1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur) ≤ y.w + P.rho * y.b + y.wl - (P.wf + P.ul + P.c) by linarith)
    linarith
  · linarith
  · have := max_le (show (1 - P.rho) * P.kUl - P.rho * P.s ≤ y.w + P.rho * y.b + y.wl - (P.wf + P.ul + P.c) - P.rho * (P.kFh - P.r) by linarith)
      (show (1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur) ≤ y.w + P.rho * y.b + y.wl - (P.wf + P.ul + P.c) - P.rho * (P.kFh - P.r) by linarith)
    linarith

theorem ach_none (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    ∃ x, Feasible P .none x ∧ cost P x = P.wf + P.ul + P.c + 0 := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have hb : P.rho * (P.c / P.rho) = P.c := mul_div_cancel₀ _ hρ.ne'
  refine ⟨⟨P.wf, P.c / P.rho, P.ul⟩, ?_, ?_⟩
  · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
      Style.onHigh, Style.onLow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [cost]; linarith

theorem ach_F (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    ∃ x, Feasible P .F x ∧ cost P x = P.wf + P.ul + P.c + P.rho * (P.kFh - P.r) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  have hb : P.rho * (P.c / P.rho) = P.c := mul_div_cancel₀ _ hρ.ne'
  refine ⟨⟨P.wf, P.c / P.rho - P.r, P.ul + P.rho * P.kFh⟩, ?_, ?_⟩
  · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
      Style.onHigh, Style.onLow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [cost]; linarith

/-- Style U attains `max U1 U2`; style FU attains `gF + max U1 U2`. Parametrised by the
high-output action value `h` and its leader cost. -/
theorem ach_U (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    ∃ x, Feasible P .U x ∧ cost P x = P.wf + P.ul + P.c +
      max ((1 - P.rho) * P.kUl - P.rho * P.s)
        ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur)) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  rcases le_total ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur))
      ((1 - P.rho) * P.kUl - P.rho * P.s) with hle | hle
  · rw [max_eq_left hle]
    have hb : P.rho * (P.c / P.rho) = P.c := mul_div_cancel₀ _ hρ.ne'
    refine ⟨⟨P.wf, P.c / P.rho - P.s, P.ul + (1 - P.rho) * P.kUl⟩, ?_, ?_⟩
    · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
        Style.onHigh, Style.onLow]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [cost]; linarith
  · rw [max_eq_right hle]
    have hb : P.rho * ((P.ur - P.wf + P.c + (1 - P.rho) * P.s) / P.rho) =
        P.ur - P.wf + P.c + (1 - P.rho) * P.s := mul_div_cancel₀ _ hρ.ne'
    refine ⟨⟨P.wf, (P.ur - P.wf + P.c + (1 - P.rho) * P.s) / P.rho,
      P.ul + (1 - P.rho) * P.kUl⟩, ?_, ?_⟩
    · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
        Style.onHigh, Style.onLow]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [cost]; linarith

theorem ach_FU (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    ∃ x, Feasible P .FU x ∧ cost P x = P.wf + P.ul + P.c + (P.rho * (P.kFh - P.r) +
      max ((1 - P.rho) * P.kUl - P.rho * P.s)
        ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur))) := by
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS
  rcases le_total ((1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur))
      ((1 - P.rho) * P.kUl - P.rho * P.s) with hle | hle
  · rw [max_eq_left hle]
    have hb : P.rho * (P.c / P.rho) = P.c := mul_div_cancel₀ _ hρ.ne'
    refine ⟨⟨P.wf, P.c / P.rho - P.s - P.r, P.ul + (P.rho * P.kFh + (1 - P.rho) * P.kUl)⟩,
      ?_, ?_⟩
    · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
        Style.onHigh, Style.onLow]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [cost]; linarith
  · rw [max_eq_right hle]
    have hb : P.rho * ((P.ur - P.wf + P.c + (1 - P.rho) * P.s) / P.rho) =
        P.ur - P.wf + P.c + (1 - P.rho) * P.s := mul_div_cancel₀ _ hρ.ne'
    refine ⟨⟨P.wf, (P.ur - P.wf + P.c + (1 - P.rho) * P.s) / P.rho - P.r,
      P.ul + (P.rho * P.kFh + (1 - P.rho) * P.kUl)⟩, ?_, ?_⟩
    · simp only [Feasible, utilHigh, utilLow, leaderCost, actionValue, costHigh, costLow,
        Style.onHigh, Style.onLow]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · simp only [cost]; linarith

end LeaderStyle.WageFloor.P2Aux

open LeaderStyle.WageFloor in
theorem solution (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    (1 ≤ P.kFh / P.r ∧ P.rho / (1 - P.rho) ≤ P.kUl / P.s → IsOptimalStyle P .none) ∧
    (P.kFh / P.r < 1 →
      (P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P → IsOptimalStyle P .FU) ∧
      (¬ (P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P) → IsOptimalStyle P .F)) ∧
    (¬ (1 ≤ P.kFh / P.r ∧ P.rho / (1 - P.rho) ≤ P.kUl / P.s) →
      ¬ (P.kFh / P.r < 1) →
      (condU' P → IsOptimalStyle P .U) ∧
      (¬ condU' P → IsOptimalStyle P .none)) := by
  have hS' := hS
  obtain ⟨hc, hρ, hρ1, hr, hs, hkFh, hkFl, hkUl, hkUh, hur, hrs⟩ := hS'
  have h1ρ : 0 < 1 - P.rho := by linarith
  -- translations of the ratio conditions
  have tA : 1 ≤ P.kFh / P.r ↔ P.r ≤ P.kFh := one_le_div hr
  have tD : P.rho / (1 - P.rho) ≤ P.kUl / P.s ↔ P.rho * P.s ≤ P.kUl * (1 - P.rho) :=
    div_le_div_iff₀ h1ρ hs
  have tD' : P.kUl / P.s < P.rho / (1 - P.rho) ↔ P.kUl * (1 - P.rho) < P.rho * P.s :=
    div_lt_div_iff₀ hs h1ρ
  have tU : condU' P ↔ (1 - P.rho) * (P.s + P.kUl) < P.wf - P.ur := Iff.rfl
  set U1 := (1 - P.rho) * P.kUl - P.rho * P.s with hU1
  set U2 := (1 - P.rho) * P.kUl + (1 - P.rho) * P.s - (P.wf - P.ur) with hU2
  set gF := P.rho * (P.kFh - P.r) with hgF
  have finish : ∀ (A : Style) (V : ℝ), (∃ x, Feasible P A x ∧ cost P x = P.wf + P.ul + P.c + V) →
      V ≤ 0 → V ≤ gF → V ≤ max U1 U2 → V ≤ gF + max U1 U2 → IsOptimalStyle P A := by
    intro A V ⟨x, hx, hcx⟩ h0 hF hU hFU
    exact ⟨x, hx, fun B y hy => hcx ▸ P2Aux.lb P hS hnc V h0 hF hU hFU B y hy⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨ha, hd⟩
    have ha' := tA.mp ha
    have hd' := tD.mp hd
    have hgF0 : 0 ≤ gF := mul_nonneg hρ.le (by linarith)
    have hU10 : 0 ≤ U1 := by rw [hU1]; linarith
    have : 0 ≤ max U1 U2 := le_trans hU10 (le_max_left _ _)
    exact finish .none 0 (P2Aux.ach_none P hS hnc) le_rfl hgF0 this (by linarith)
  · intro ha
    have ha' : P.kFh < P.r := (div_lt_one hr).mp ha
    have hgF0 : gF < 0 := mul_neg_of_pos_of_neg hρ (by linarith)
    refine ⟨?_, ?_⟩
    · rintro ⟨hd, hu⟩
      have hd' := tD'.mp hd
      have hu' := tU.mp hu
      have hm : max U1 U2 < 0 := max_lt (by rw [hU1]; linarith) (by rw [hU2]; linarith)
      exact finish .FU (gF + max U1 U2) (P2Aux.ach_FU P hS hnc) (by linarith) (by linarith)
        (by linarith) le_rfl
    · intro hn
      have hm : 0 ≤ max U1 U2 := by
        by_cases hd : P.kUl / P.s < P.rho / (1 - P.rho)
        · have hu : ¬ condU' P := fun hu => hn ⟨hd, hu⟩
          have hu' : ¬ (1 - P.rho) * (P.s + P.kUl) < P.wf - P.ur := fun h => hu (tU.mpr h)
          exact le_trans (by rw [hU2]; linarith) (le_max_right _ _)
        · have hd' : ¬ P.kUl * (1 - P.rho) < P.rho * P.s := fun h => hd (tD'.mpr h)
          exact le_trans (by rw [hU1]; linarith) (le_max_left _ _)
      exact finish .F gF (P2Aux.ach_F P hS hnc) hgF0.le le_rfl (by linarith) (by linarith)
  · intro hn1 hn2
    have ha : 1 ≤ P.kFh / P.r := not_lt.mp hn2
    have ha' := tA.mp ha
    have hgF0 : 0 ≤ gF := mul_nonneg hρ.le (by linarith)
    have hd : ¬ P.rho / (1 - P.rho) ≤ P.kUl / P.s := fun h => hn1 ⟨ha, h⟩
    have hd' : ¬ P.rho * P.s ≤ P.kUl * (1 - P.rho) := fun h => hd (tD.mpr h)
    refine ⟨?_, ?_⟩
    · intro hu
      have hu' := tU.mp hu
      have hm : max U1 U2 < 0 := max_lt (by rw [hU1]; linarith) (by rw [hU2]; linarith)
      exact finish .U (max U1 U2) (P2Aux.ach_U P hS hnc) hm.le (by linarith) le_rfl (by linarith)
    · intro hu
      have hu' : ¬ (1 - P.rho) * (P.s + P.kUl) < P.wf - P.ur := fun h => hu (tU.mpr h)
      have hm : 0 ≤ max U1 U2 := le_trans (by rw [hU2]; linarith) (le_max_right _ _)
      exact finish .none 0 (P2Aux.ach_none P hS hnc) le_rfl hgF0 hm (by linarith)
