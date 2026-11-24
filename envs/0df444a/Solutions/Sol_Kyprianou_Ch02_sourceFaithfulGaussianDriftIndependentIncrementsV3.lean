-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianDriftIndependentIncrementsV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:09:42.541817+00:00
-- url     : https://prove2.me/submissions/798ba100-12ac-4b66-be2c-7e39b6392988

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_Kyprianou_Ch01_mathlibIndepIncrements_toLeanLevy
import Theorems.Thm_Continuous_isCadlag
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => B.W t ω
  have hI := Kyprianou.Ch01.mathlibIndepIncrements_toLeanLevy P X
    B.hasIndepIncrements_readable
  intro n t ht
  let f (k : Fin n) (x : ℝ) :=
    (σ : ℝ) * x - a * ((t k.succ : ℝ) - (t k.castSucc : ℝ))
  have hi := (hI n t ht).comp f
    (fun k => (measurable_const.mul measurable_id).sub measurable_const)
  convert hi using 1
  funext k ω
  dsimp [f, X, Function.comp_def, increment]
  ring
