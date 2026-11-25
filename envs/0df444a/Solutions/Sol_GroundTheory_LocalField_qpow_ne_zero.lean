-- Prove2me | solution 1 for GroundTheory.LocalField.qpow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:59.295802+00:00
-- url     : https://prove2.me/submissions/1fa5658b-d0a2-4e91-ade1-d75685c05c75

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
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
theorem _root_.solution (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex]
  exact Complex.exp_ne_zero _
end GroundTheory.LocalField
