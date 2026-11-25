-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PositiveDriftAlmostSurePositivePersistenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:47:32.850333+00:00
-- url     : https://prove2.me/submissions/96df0ff5-7d0e-43bd-8c7e-d635571e2f09

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PositiveDriftNoImmediateDowncrossingV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (d : ℝ) (hd : 0 < d)
    (h : ∀ᵐ ω ∂P, Tendsto (fun t : NNReal => X t ω / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    let τ : Ω → WithTop NNReal :=
      fun ω => sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t ω < 0}
    0 < P {ω : Ω | 0 < τ ω} := by
  dsimp only
  let τ : Ω → WithTop NNReal :=
    fun ω => sInf {u : WithTop NNReal |
      ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t ω < 0}
  let Good : Set Ω := {ω | 0 < τ ω}
  have hAE : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [h] with ω hω
    exact Kyprianou.Ch04.exercise49PositiveDriftNoImmediateDowncrossingV1
      (fun t => X t ω) d hd hω
  have hnull : P Goodᶜ = 0 := (mem_ae_iff).mp hAE
  have hsub : P Set.univ ≤ P Good + P Goodᶜ := by
    simpa only [union_compl_self] using (measure_union_le Good Goodᶜ)
  have hOne : (1 : ENNReal) ≤ P Good := by
    simpa [hnull] using hsub
  exact lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hOne
