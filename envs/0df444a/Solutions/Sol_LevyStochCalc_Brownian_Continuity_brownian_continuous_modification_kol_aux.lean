-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.brownian_continuous_modification_kol_aux
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:42:06.600216+00:00
-- url     : https://prove2.me/submissions/4c19ce8b-318c-4d9d-a84f-0bd451023254

import Definitions.Def_LevyStochCalc_Brownian_Continuity_F001
import Definitions.Def_SourceProof_c5c83cf022c9fd5765bb05bb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2 :=
  Prove2MeSourceProof.h_c5c83cf022c9fd5765bb05bb X h_meas h_increment hst
