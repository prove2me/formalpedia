-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_phi_quotient_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:57:03.199124+00:00
-- url     : https://prove2.me/submissions/19641a01-ce78-4ba1-ac65-59a6008535a7

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_coefficient_when_positive_zero_root
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_coefficient_when_zero_root
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W) :
    (∀ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds d)) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) := by
  have hzero : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl zero_lt_one).2
  have hconv := source_result81_law_laplace_convex Ω P D ψ hψ
  have hφ0 : 0 ≤ Phi ψ 0 := ((hW 0 le_rfl).1.2.1).1
  rcases eq_or_lt_of_le hφ0 with heq | hpos
  · exact source_result81_coefficient_when_zero_root ψ W hW hconv hzero heq.symm
  · exact source_result81_coefficient_when_positive_zero_root ψ W hW hconv hzero hpos
