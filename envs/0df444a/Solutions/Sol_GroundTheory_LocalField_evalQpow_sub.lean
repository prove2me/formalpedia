-- Prove2me | solution 1 for GroundTheory.LocalField.evalQpow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:24.991998+00:00
-- url     : https://prove2.me/submissions/d9183c1c-8334-4c63-9cb6-fc8afe618a87

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral

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
theorem _root_.solution (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P - Q) s = evalQpow K P s - evalQpow K Q s := map_sub _ _ _
end GroundTheory.LocalField
