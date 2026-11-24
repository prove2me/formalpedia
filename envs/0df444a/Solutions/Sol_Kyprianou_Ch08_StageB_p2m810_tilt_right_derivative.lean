-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_tilt_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:09:54.065955+00:00
-- url     : https://prove2.me/submissions/f16f79cd-ecdf-4332-812c-fba7592e9b78

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful reflected exit proof. -/
theorem solution : ∀ (w : ℝ → ℝ) (θ a d : ℝ),
      HasDerivWithinAt w d (Ici a) a →
      HasDerivWithinAt (tiltedScale θ w)
        (derivWithin (tiltedScale θ w) (Ici a) a) (Ici a) a ∧
      derivWithin (tiltedScale θ w) (Ici a) a + θ * tiltedScale θ w a =
        Real.exp (-θ*a) * d := by
  intro w θ a d hd
  have he : HasDerivAt (fun y : ℝ => Real.exp (-θ*y))
      (Real.exp (-θ*a) * (-θ)) a := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id a).const_mul (-θ)).exp)
  have h := he.hasDerivWithinAt.mul hd
  have ht : HasDerivWithinAt (tiltedScale θ w)
      (Real.exp (-θ*a) * (-θ) * w a + Real.exp (-θ*a) * d) (Ici a) a := h
  have hv := ht.derivWithin (uniqueDiffWithinAt_Ici a)
  refine ⟨hv.symm ▸ ht, ?_⟩
  rw [hv]
  unfold tiltedScale
  ring
