-- Prove2me | solution 1 for ModernOnlineLearning.OMD.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:06:36.528822+00:00
-- url     : https://prove2.me/submissions/05e1a185-4264-4917-ae76-769f222a9d35

import Definitions.Def_ModernOnlineLearning_OMD_Defs

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : Set E) (ψ : E → ℝ)
    (hstrict : StrictConvexOn ℝ X ψ)
    (hdiff : DifferentiableOn ℝ ψ (interior X))
    (x y z : E) (hx : x ∈ interior X) (hy : y ∈ interior X) (hz : z ∈ X) :
    BeckTeboulleMD.EMDA.bregman ψ z x +
      BeckTeboulleMD.EMDA.bregman ψ x y -
      BeckTeboulleMD.EMDA.bregman ψ z y =
        (fderiv ℝ ψ y - fderiv ℝ ψ x) (z - x) := by
  simp only [BeckTeboulleMD.EMDA.bregman, ContinuousLinearMap.sub_apply, map_sub]
  ring

