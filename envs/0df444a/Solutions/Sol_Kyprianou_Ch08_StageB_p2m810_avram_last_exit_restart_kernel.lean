-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_avram_last_exit_restart_kernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:03:30.059342+00:00
-- url     : https://prove2.me/submissions/6ae2c756-ed22-45e1-b360-0b160ad465a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_avram_last_exit_restart_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_pathwise_last_exit_restart_payoff
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q y : ℝ) (hq : 0 < q) (hy : 0 < y)
    (hDrift : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => A.X t ω) atTop atTop) :
    (∫ ω, discountedPositiveLastExit A.X q y ω ∂P) = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted A.X (y + A.X t ω) η) ∂P))
      (tauMinus (shifted A.X y) 0 ω) ∂P) := by
  calc
    _ = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        discountedAt q (lastNegativeVisit (fun s (_ : Unit) => y + A.X (t+s) ω) ()))
      (tauMinus (shifted A.X y) 0 ω) ∂P) := by
      apply integral_congr_ae
      filter_upwards [hDrift] with ω hw
      exact p2m810_pathwise_last_exit_restart_payoff (fun t => A.X t ω)
        y q hy (A.X_zero ω) (A.rightCont ω 0) hw
    _ = _ := p2m810_avram_last_exit_restart_integral Ω P F A q y hq
