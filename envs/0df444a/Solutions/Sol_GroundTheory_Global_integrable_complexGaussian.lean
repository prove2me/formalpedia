-- Prove2me | solution 1 for GroundTheory.Global.integrable_complexGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:36:01.176801+00:00
-- url     : https://prove2.me/submissions/a304562a-67d6-4d25-8eef-dbd24521f8e3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
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
theorem _root_.solution (m : ℤ) :
    Integrable (complexGaussian m) complexPlaceMeasure := by
  simpa using integrable_norm_pow_smul_complexGaussian' m 0
end GroundTheory.Global
