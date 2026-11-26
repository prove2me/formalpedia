-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_finite_large_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:03:23.109018+00:00
-- url     : https://prove2.me/submissions/e658e00a-d4f0-4b9b-8d81-a37addf1b15b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_ProofPreparation_finite_large_jumps_of_nnreal_cadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    {s : NNReal | 0 < s ∧ s ≤ T ∧ ρ ≤ |X s-L s|}.Finite := by
  have hf := Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag X
    (fun s => (hCad s).1) (fun s hs => ⟨L s,hLeft s hs⟩) T (ρ/2) (by positivity)
  apply hf.subset
  intro s hs
  exact ⟨hs.1,hs.2.1,L s,hLeft s hs.1,by linarith [hs.2.2]⟩
