-- Prove2me | solution 1 for Kyprianou.Ch01.mathlibBrownianStationarity_toLeanLevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:02.015424+00:00
-- url     : https://prove2.me/submissions/4097333a-1c20-4e67-892b-34a9ce13171a

import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_LeanLevy_Processes_StochasticProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Equal Gaussian laws of equally long increments imply LeanLevy stationary increments. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (h : ProbabilityTheory.IsPreBrownianReal X P) :
    ProbabilityTheory.HasStationaryIncrements X P := by
  intro s u
  have ha := h.hasLaw_sub (s + u) s
  have hb := h.hasLaw_sub u 0
  have hdist :
      nndist (((s + u : ℝ≥0) : ℝ)) (s : ℝ) =
        nndist (u : ℝ) (0 : ℝ) := by
    simpa [NNReal.coe_add, add_comm] using
      (nndist_add_right (u : ℝ) (0 : ℝ) (s : ℝ))
  have hmeasure :
      gaussianReal 0 (nndist (((s + u : ℝ≥0) : ℝ)) (s : ℝ)) =
        gaussianReal 0 (nndist (u : ℝ) (0 : ℝ)) :=
    congrArg (gaussianReal (0 : ℝ)) hdist
  have ha' : HasLaw (X (s + u) - X s)
      (gaussianReal 0 (nndist (u : ℝ) (0 : ℝ))) P :=
    Eq.mp (congrArg (fun nu : Measure ℝ =>
      HasLaw (X (s + u) - X s) nu P) hmeasure) ha
  change IdentDistrib
    (fun ω => X (s + u) ω - X s ω)
    (fun ω => X u ω - X 0 ω) P P
  exact ha'.identDistrib hb
