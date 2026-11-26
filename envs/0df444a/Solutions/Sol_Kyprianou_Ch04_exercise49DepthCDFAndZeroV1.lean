-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthCDFAndZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:34:39.148281+00:00
-- url     : https://prove2.me/submissions/0bde2712-e190-4003-8b65-38287e9727b0

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49FinitePathLowerBoundAEV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthIsLUBV1
import Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalClockIffV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The rational depth distribution gives survival probabilities and vanishes on no ruin. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (hInf : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop)
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let V : Ω → ℝ := fun w => (⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal
    (∀ x : ℝ, 0 ≤ x →
      P (V ⁻¹' Iic x) = P {w | (sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x + X t w < 0}) = ⊤}) ∧
    (∀ᵐ w ∂P.restrict {w | τ w = ⊤}, V w = 0) := by
  dsimp only
  have hBound := Kyprianou.Ch04.exercise49FinitePathLowerBoundAEV1 P X hX hm hc hInf
  have hL : ∀ᵐ w ∂P, IsLUB (range (fun t : NNReal => -X t w))
      (⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal := by
    filter_upwards [hBound] with w h
    exact Kyprianou.Ch04.exercise49RationalDepthIsLUBV1 (fun t => X t w)
      (congrFun hX.start_zero w) (fun t => (hc w t).1) h
  constructor
  · intro x hx
    apply measure_congr
    filter_upwards [hL] with w hw
    change (((⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal ≤ x)) =
      ((sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ x + X t w < 0}) = ⊤)
    apply propext
    rw [Kyprianou.Ch04.exercise49SurvivalClockIffV1
      (fun t => X t w) (congrFun hX.start_zero w) x hx]
    constructor
    · intro h t
      linarith [hw.1 (mem_range_self t)]
    · intro h
      apply hw.2
      rintro _ ⟨t, rfl⟩
      linarith [h t]
  · have hD : MeasurableSet {w | τ w = ⊤} := hτm (measurableSet_singleton ⊤)
    filter_upwards [hL.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem hD] with w hw hD'
    have hSurv := (Kyprianou.Ch04.exercise49SurvivalClockIffV1
      (fun t => X t w) (congrFun hX.start_zero w) 0 le_rfl).mp
      (by simpa only [zero_add] using (hτ w).symm.trans hD')
    apply le_antisymm
    · apply hw.2
      rintro _ ⟨t, rfl⟩
      linarith [hSurv t]
    · simpa [congrFun hX.start_zero w] using hw.1 (mem_range_self (0 : NNReal))
