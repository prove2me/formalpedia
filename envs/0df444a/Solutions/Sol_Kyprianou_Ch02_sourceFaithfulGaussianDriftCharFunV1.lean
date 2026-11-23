-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:03:32.112921+00:00
-- url     : https://prove2.me/submissions/6f748745-b8d3-4217-92d7-a75c31ca19ef

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open LevyStochCalc.Brownian Kyprianou Kyprianou.Ch02

theorem solution
    (a : ℝ) (σ : ℝ≥0)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (Xgauss : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Xgauss t)) ξ = Complex.exp ((((t : ℝ) : ℂ)) *
          (-Complex.I * (a : ℂ) * (ξ : ℂ) -
            (((σ : ℝ) ^ 2 * ξ ^ 2 / 2 : ℝ) : ℂ)))  := by
  intro t ξ
  have hW : HasLaw (B.W (t : ℝ)) (gaussianReal 0 t) P :=
    B.hasLaw_eval_readable t
  have hscaled := gaussianReal_mul_const hW (σ : ℝ)
  have hshift := gaussianReal_sub_const hscaled (a * (t : ℝ))
  have hX : Xgauss t =
      (fun ω => B.W (t : ℝ) ω * (σ : ℝ) - a * (t : ℝ)) := by
    funext ω
    rw [hgauss t ω]
    ring
  rw [hX, hshift.map_eq, charFun_gaussianReal]
  congr 1
  simp only [mul_zero, zero_sub, NNReal.coe_mul, NNReal.coe_mk]
  push_cast
  ring
