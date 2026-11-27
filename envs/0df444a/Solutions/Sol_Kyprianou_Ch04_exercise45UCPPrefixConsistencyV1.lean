-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45UCPPrefixConsistencyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:30:39.169037+00:00
-- url     : https://prove2.me/submissions/d9b8f76c-ad28-4b99-ac40-fb7dfe5d3334

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise45ClippedGridPrefixEqV1
import Theorems.Thm_Kyprianou_Ch04_exercise45OuterUCPPrefixLimitV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- UCP stochastic integrals preserve equality of the integrands through a random clock. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X H K I L : NNReal → Ω → ℝ) (τ : Ω → NNReal)
    (hI : Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X H I)
    (hL : Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X K L)
    (hHK : ∀ᵐ w ∂P, ∀ t ≤ τ w, H t w = K t w) :
    ∀ᵐ w ∂P, ∀ t ≤ τ w, I t w = L t w := by
  let G (W : NNReal → Ω → ℝ) (T : NNReal) (j : ℕ) (t : NNReal) (w : Ω) :=
    ∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      W u w * (X (min t v) w - X (min t u) w)
  apply Kyprianou.Ch04.exercise45OuterUCPPrefixLimitV1 P (G H) (G K) I L τ hI hL
  filter_upwards [hHK] with w hw
  intro T j t ht
  exact Kyprianou.Ch04.exercise45ClippedGridPrefixEqV1 X H K w T t j
    (fun u hu => hw u (hu.trans ht))
