-- Prove2me | solution 1 for KyleProduction.Monopoly.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:51:26.775872+00:00
-- url     : https://prove2.me/submissions/52064301-a5d3-41b6-9d7f-024becf9d84d

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model
import Theorems.Thm_KyleProduction_Monopoly_trading_stage
import Theorems.Thm_KyleProduction_Monopoly_trading_profit
import Theorems.Thm_KyleProduction_Monopoly_production_stage
import Theorems.Thm_KyleProduction_Monopoly_firm_value_law

open MeasureTheory ProbabilityTheory

namespace Aux_p1
open KyleProduction.Monopoly

theorem obj_eq (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat) (he : IsLinEq P q e) :
    objective P q e = P.ω * (q * (postMean P - q)) + |q| / 2 * kappa P := by
  unfold objective
  rw [(firm_value_law P hS q).2, trading_profit P hS q e he]

theorem qHat_pos (P : Params) (hS : P.Standing) (hm : 0 < postMean P) : 0 < qHat P := by
  obtain ⟨-, -, -, hω, -⟩ := hS
  unfold qHat
  have : 0 ≤ kappa P := Real.sqrt_nonneg _
  positivity

end Aux_p1

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (hm : 0 < postMean P)
    (q : ℝ) (e : LinStrat) :
    IsEquilibrium P q e ↔ (q = qHat P ∧ e = eqStrat P (qHat P)) := by
  have hqh := Aux_p1.qHat_pos P hS hm
  have hlinH : IsLinEq P (qHat P) (eqStrat P (qHat P)) :=
    (trading_stage P hS (qHat P) hqh _).2 rfl
  constructor
  · rintro ⟨hlin, hmax⟩
    have h1 := hmax (qHat P) (eqStrat P (qHat P)) hlinH
    rw [Aux_p1.obj_eq P hS _ _ hlinH, Aux_p1.obj_eq P hS _ _ hlin] at h1
    have hq : q = qHat P := by
      by_contra hne
      have := production_stage P hS hm q hne
      linarith
    subst hq
    exact ⟨rfl, (trading_stage P hS _ hqh e).1 hlin⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨hlinH, fun q' e' he' => ?_⟩
    rw [Aux_p1.obj_eq P hS _ _ hlinH, Aux_p1.obj_eq P hS _ _ he']
    by_cases hq' : q' = qHat P
    · rw [hq']
    · exact (production_stage P hS hm q' hq').le
