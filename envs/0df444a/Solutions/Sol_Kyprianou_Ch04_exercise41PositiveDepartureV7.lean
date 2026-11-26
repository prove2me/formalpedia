-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PositiveDepartureV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:52.60353+00:00
-- url     : https://prove2.me/submissions/e885552a-5a6c-40dc-9fc9-ee073e1825f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroClockFamilyV12
import Theorems.Thm_Kyprianou_Ch04_exercise41StoppedPositiveGermV12
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, L.X s w = 0 →
      ∃ ε : NNReal, 0 < ε ∧ ∀ u : NNReal, 0 < u → u < ε →
        0 < L.X (s + u) w := by
  obtain ⟨τ,hτ,hcover⟩ := exercise41ZeroClockFamilyV12 P F L hBV hd
  have hG (j N : ℕ) := exercise41StoppedPositiveGermV12 P F L hBV hd
    (τ j N) (hτ j N)
  have hall : ∀ᵐ w ∂P, ∀ j N : ℕ, ∃ ε : NNReal, 0 < ε ∧
    ∀ u : NNReal, 0 < u → u < ε →
      0 < L.X (τ j N w + u) w - L.X (τ j N w) w :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (hG j))
  filter_upwards [hcover,hall] with w hw hg
  intro s hs
  obtain ⟨j,N,hj⟩ := hw s hs
  obtain ⟨ε,hε,hg'⟩ := hg j N
  refine ⟨ε,hε,?_⟩
  intro u hu hlt
  have H := hg' u hu hlt
  rw [hj,hs,sub_zero] at H
  exact H
