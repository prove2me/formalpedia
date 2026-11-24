-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_source_tilt_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:13.186459+00:00
-- url     : https://prove2.me/submissions/c66d5dcd-d911-42bb-b55c-4ec6a839524e

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_tilt_right_derivative
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a θ : ℝ), 0 ≤ q → 0 < a →
      HasDerivWithinAt (tiltedScale θ (W q))
        (derivWithin (tiltedScale θ (W q)) (Ici a) a) (Ici a) a ∧
      derivWithin (tiltedScale θ (W q)) (Ici a) a + θ * tiltedScale θ (W q) a =
        Real.exp (-θ*a) * derivWithin (W q) (Ici a) a := by
  intro Ω mΩ P hP D ψ W hψ hW q a θ hq ha
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, hd, _⟩ := h8 Ω P D ψ W hψ hW q hq
  obtain ⟨dl, dr, hl, hr, hdl, hdr, heq⟩ := hd a ha
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici a)]
  exact p2m810_tilt_right_derivative (W q) θ a dr hr
