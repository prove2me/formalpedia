-- Prove2me | solution 1 for KyleProduction.Monopoly.price_demand
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:43:24.740689+00:00
-- url     : https://prove2.me/submissions/57dbb887-a26c-4f7a-bf18-d0d5b6b497ae

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model
set_option autoImplicit false

open KyleProduction.Monopoly

theorem solution (P : Params) (hS : P.Standing) (q : ℝ) (hq : 0 < q) (a u : ℝ) :
    price (eqStrat P q) (orderFlow (eqStrat P q) q (a, u)) =
      1 / 2 * q * ((postMean P - q) + (a - q) + 1 / P.Su * kappa P * u) ∧
    demand (eqStrat P q) (firmValue q a) =
      -(Real.sqrt P.Su / Real.sqrt (postVar P)) * (postMean P - q) +
        Real.sqrt P.Su / Real.sqrt (postVar P) * (a - q) := by
  obtain ⟨hSa, hSθ, hSu, -, -⟩ := hS
  have hpv : 0 < postVar P := by unfold postVar; positivity
  have hs : 0 < Real.sqrt P.Su := Real.sqrt_pos.2 hSu
  have hv : 0 < Real.sqrt (postVar P) := Real.sqrt_pos.2 hpv
  have hκ : kappa P = Real.sqrt P.Su * Real.sqrt (postVar P) := by
    unfold kappa postVar
    rw [← Real.sqrt_mul hSu.le]
    congr 1; ring
  have hss : Real.sqrt P.Su * Real.sqrt P.Su = P.Su := Real.mul_self_sqrt hSu.le
  have hdem : demand (eqStrat P q) (firmValue q a) =
      -(Real.sqrt P.Su / Real.sqrt (postVar P)) * (postMean P - q) +
        Real.sqrt P.Su / Real.sqrt (postVar P) * (a - q) := by
    unfold demand eqStrat firmValue
    simp only
    field_simp
  refine ⟨?_, hdem⟩
  unfold price orderFlow
  simp only [eqStrat] at hdem ⊢
  rw [hdem, hκ]
  generalize Real.sqrt P.Su = s at *
  generalize Real.sqrt (postVar P) = v at *
  rw [← hss]
  generalize postMean P = m
  field_simp
  ring
