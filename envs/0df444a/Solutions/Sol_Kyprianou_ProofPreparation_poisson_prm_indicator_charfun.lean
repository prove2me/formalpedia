-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_indicator_charfun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:26:47.544044+00:00
-- url     : https://prove2.me/submissions/59bd848e-1cf5-451d-a5c6-9f7fdc9af12f

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The characteristic function of the indicator Poisson integral. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤)
    (ξ : ℝ) :
    charFun (P.map (fun ω => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp (((m A).toReal : ℂ) *
        (Complex.exp (((ξ : ℝ) : ℂ) * Complex.I) - 1)) := by
  have hEval :
      (fun ω => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
        (poissonRandomMeasure K Y ω)) =
      (fun ω => (poissonRandomMeasure K Y ω A).toReal) := by
    funext ω
    exact integral_indicator_one hA
  rw [hEval]
  exact charFun_natCast_poissonRandomMeasure_apply hd hA hfin ξ
