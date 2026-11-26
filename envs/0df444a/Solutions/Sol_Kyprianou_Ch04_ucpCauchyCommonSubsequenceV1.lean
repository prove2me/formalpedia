-- Prove2me | solution 1 for Kyprianou.Ch04.ucpCauchyCommonSubsequenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:09:00.599892+00:00
-- url     : https://prove2.me/submissions/cbff0c9d-9262-4c12-a49c-50128cf6f8c8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ucpDiagonalGeometricV1
import Theorems.Thm_Kyprianou_Ch04_expandingGeometricUniformCauchyV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

/-- Compose the probabilistic diagonal and deterministic uniform Cauchy theorem. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    (P : Measure Ω) (X : ℕ → NNReal → Ω → E)
    (hc : ∀ i : ℕ, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i < dist (X m t w) (X n t w)} ≤
        (2⁻¹ : ENNReal)^i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ w ∂P, ∀ T : NNReal,
      UniformCauchySeqOn (fun n t => X (k n) t w) atTop (Icc 0 T) := by
  obtain ⟨k,hk,h⟩ := Kyprianou.Ch04.ucpDiagonalGeometricV1 P X hc
  refine ⟨k,hk,?_⟩
  filter_upwards [h] with w hw
  exact Kyprianou.Ch04.expandingGeometricUniformCauchyV1 (fun n t => X (k n) t w) hw
