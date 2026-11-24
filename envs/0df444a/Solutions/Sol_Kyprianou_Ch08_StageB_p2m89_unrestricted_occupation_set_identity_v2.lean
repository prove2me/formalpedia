-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_unrestricted_occupation_set_identity_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:19:41.043633+00:00
-- url     : https://prove2.me/submissions/9a3f4a2f-b802-4dd4-99f5-88885a5b1174
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_tilted_scale_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_translated_killed_occupation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_killing_barrier_exhaustion
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_exhaustion
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

/-- 8.9: unrestricted occupation identity on measurable sets. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q →
      ∀ (A : Set ℝ), MeasurableSet A →
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal
        (unrestrictedPotentialDensity ψ q (W q) (y - x)))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq A hA
  obtain ⟨hm, hl⟩ := p2m89_tilted_scale_limit D ψ W hψ hW q hq
  have h1 := p2m89_density_exhaustion ψ W q x A hA (hW q hq.le) hm hl
  have h2 := p2m89_killing_barrier_exhaustion D ψ W hψ hW q hq x A hA
  exact tendsto_nhds_unique (h1.congr' (Eventually.of_forall
    (p2m89_translated_killed_occupation D ψ W hψ hW q hq x A hA))) h2
