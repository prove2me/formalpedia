-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_eq_fourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:00.906427+00:00
-- url     : https://prove2.me/submissions/3ca50c99-f034-4ba1-9736-e646e0227ef0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.traceFormℂ_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (f : ℂ → ℂ) :
    complexFourier f =
      VectorFourier.fourierIntegral 𝐞 complexPlaceMeasure traceFormℂ.toLinearMap₁₂ f := by
  funext w
  simp [complexFourier, VectorFourier.fourierIntegral]
end GroundTheory.Global
