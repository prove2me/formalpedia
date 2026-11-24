-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianDriftIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:08:46.190112+00:00
-- url     : https://prove2.me/submissions/e26aa8a0-5693-44ad-a011-068291cb340b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_ProbabilityTheory_hasIndependentIncrements_iff_hasIndepIncrements
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0) :
    HasIndependentIncrements (fun (t : ℝ≥0) (ω : Ω) =>
      (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P := by
  intro n t ht
  have hi := (hasIndependentIncrements_iff_hasIndepIncrements.mpr
    B.hasIndepIncrements_readable) n t ht
  have h := hi.comp
    (fun k : Fin n => fun x : ℝ =>
      (σ : ℝ) * x - a * ((t k.succ : ℝ) - (t k.castSucc : ℝ)))
    (fun _ => (measurable_const.mul measurable_id).sub measurable_const)
  convert h using 1
  funext k ω
  dsimp [Function.comp_def, increment]
  ring
