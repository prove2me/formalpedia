-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_payoff_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:57:55.957791+00:00
-- url     : https://prove2.me/submissions/8315ae15-ee43-4aa6-8ff3-68abfa16de51

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_post_stopped_reward_shift
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_shifted_killed_integral_tonelli
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (hq : 0 < q) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a)
    (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hreward : Measurable reward)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue)) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, if U ω < L ω then disc (τ ω) *
        reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  intro U L τ disc
  let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
    if U ω < L ω then disc t *
      (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
  calc
    _ = ∫⁻ ω, ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue ∂P := by
      refine lintegral_congr fun ω => ?_
      by_cases h : U ω < L ω
      · rw [if_pos h]
        exact p2m87_qpos_factor_post_stopped_reward_shift X q a x ha hx hxa A hA
          reward hreward_value ω h
      · simp [R, h]
    _ = _ := p2m87_qpos_shifted_killed_integral_tonelli D X hpath q a x A hA
