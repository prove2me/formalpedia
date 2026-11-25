-- Prove2me | solution 1 for GroundTheory.LocalField.residueCard_nnreal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:49:14.616664+00:00
-- url     : https://prove2.me/submissions/b202767a-8269-4a77-bdd8-93cec69bfb8a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_residueCard_ne_zero

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
theorem _root_.solution : (residueCard K : ℝ≥0) ≠ 0 := by
  exact_mod_cast residueCard_ne_zero
end GroundTheory.LocalField
