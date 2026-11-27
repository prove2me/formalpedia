-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45UCPIndistinguishableCongrV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:11:57.256991+00:00
-- url     : https://prove2.me/submissions/326591b3-2d0e-44cc-8b81-0aca5460eb06

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A simultaneous almost-sure modification preserves clipped-grid UCP. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X H I Y K J : NNReal → Ω → ℝ)
    (hEq : ∀ᵐ w ∂P, ∀ t, X t w = Y t w ∧ H t w = K t w ∧ I t w = J t w)
    (hU : IsStochasticIntegralInProbabilityV2 P X H I) :
    IsStochasticIntegralInProbabilityV2 P Y K J := by
  intro T e he
  apply (hU T e he).congr'
  apply Eventually.of_forall
  intro n
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hEq] with w hw
  have hX : ∀ t, X t w = Y t w := fun t => (hw t).1
  have hH : ∀ t, H t w = K t w := fun t => (hw t).2.1
  have hI : ∀ t, I t w = J t w := fun t => (hw t).2.2
  change (∃ t : NNReal, t ≤ T ∧ e ≤ |(∑ k ∈ Finset.range n,
    H (T * (k : NNReal) / (n : NNReal)) w *
    (X (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
     X (min t (T * (k : NNReal) / (n : NNReal))) w)) - I t w|) =
    (∃ t : NNReal, t ≤ T ∧ e ≤ |(∑ k ∈ Finset.range n,
    K (T * (k : NNReal) / (n : NNReal)) w *
    (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
     Y (min t (T * (k : NNReal) / (n : NNReal))) w)) - J t w|)
  simp only [hX,hH,hI]
