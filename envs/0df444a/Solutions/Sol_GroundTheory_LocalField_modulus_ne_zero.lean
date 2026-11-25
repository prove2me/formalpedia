-- Prove2me | solution 1 for GroundTheory.LocalField.modulus_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:01:27.799343+00:00
-- url     : https://prove2.me/submissions/a5edf73e-49c8-4812-aea3-61f219de3c88

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_modulus_pos

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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {x : K} (hx : x ≠ 0) : modulus x ≠ 0 := (modulus_pos hx).ne'
end GroundTheory.LocalField
