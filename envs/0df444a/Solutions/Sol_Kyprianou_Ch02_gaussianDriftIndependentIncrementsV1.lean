-- Prove2me | solution 1 for Kyprianou.Ch02.gaussianDriftIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:15:17.578009+00:00
-- url     : https://prove2.me/submissions/fcc61abc-1597-4dbd-9f5f-0202f6108e65

import Theorems.Thm_Kyprianou_Ch01_mathlibIndepIncrements_toLeanLevy
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
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
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0)
 :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P
    := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => B.W (t : ℝ) ω
  have hI : HasIndependentIncrements X P :=
    Kyprianou.Ch01.mathlibIndepIncrements_toLeanLevy P X
      (LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements_readable B)
  intro n t ht
  let f (k : Fin n) (x : ℝ) :=
    (σ : ℝ) * x - a * ((t k.succ : ℝ) - (t k.castSucc : ℝ))
  have hi := (hI n t ht).comp f (fun k =>
    (measurable_const.mul measurable_id).sub measurable_const)
  have heq :
      (fun k : Fin n => f k ∘ increment X (t k.castSucc) (t k.succ)) =
      (fun k : Fin n => increment
        (fun t ω => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
        (t k.castSucc) (t k.succ)) := by
    funext k ω
    dsimp [f, X, Function.comp_def, increment]
    ring
  exact (congrArg (fun F => iIndepFun F P) heq).mp hi
