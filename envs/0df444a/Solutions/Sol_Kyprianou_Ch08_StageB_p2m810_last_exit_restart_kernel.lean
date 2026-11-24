-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_last_exit_restart_kernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:54:33.173436+00:00
-- url     : https://prove2.me/submissions/e7997e25-b186-4136-bb55-dc1239475315
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_restart_ae_transfer
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_avram_last_exit_restart_kernel
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y)
    (hDrift : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => D.X t ω) atTop atTop) :
    (∫ ω, discountedPositiveLastExit D.X q y ω ∂P) =
      ∫ ω, WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) *
          (∫ η, discountedAt q (lastExitShifted D.X (y + D.X t ω) η) ∂P))
        (tauMinus (shifted D.X y) 0 ω) ∂P := by
  obtain ⟨ψ,W,hψ,_⟩ := source_result8_1_v2 Ω P D
  obtain ⟨F,A,heq,_⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hA : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => A.X t ω) atTop atTop := by
    filter_upwards [heq,hDrift] with ω he hd
    simpa only [he] using hd
  exact p2m810_last_exit_restart_ae_transfer Ω P A.X D.X q y heq
    (p2m810_avram_last_exit_restart_kernel Ω P F A q y hq hy hA)
