-- Prove2me | solution 1 for GroundTheory.LocalField.differentiable_qpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:04.81235+00:00
-- url     : https://prove2.me/submissions/4f563f05-9177-4bbe-b24c-e00dadfc8cea

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Theorems.Thm_GroundTheory_LocalField_residueCard_ne_zero_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl residueCard_ne_zero_complex)
end GroundTheory.LocalField
