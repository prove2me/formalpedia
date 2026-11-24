-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_9_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:16:25.621383+00:00
-- url     : https://prove2.me/submissions/e2d94190-d14e-4653-b454-c8dc12b0b49f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_differentiable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_unrestricted_occupation_set_identity_v2
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB

/-- Corrected source result 8.9: displacement is destination minus origin. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x : ℝ), 0 < q →
        DifferentiableAt ℝ (Phi ψ) q ∧
        ∃ U : Measure ℝ,
          IsResolvent P (shifted D.X x) q U ∧
          U = volume.withDensity
            (fun y : ℝ =>
              ENNReal.ofReal
                (unrestrictedPotentialDensity ψ q (W q) (y-x))) := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq
  refine ⟨p2m89_phi_differentiable Ω P D ψ W hψ hW q hq, ?_⟩
  refine ⟨_, ?_, rfl⟩
  refine ⟨le_of_lt hq, ?_⟩
  intro A hA
  exact p2m89_unrestricted_occupation_set_identity_v2 Ω P D ψ W hψ hW q x hq A hA
