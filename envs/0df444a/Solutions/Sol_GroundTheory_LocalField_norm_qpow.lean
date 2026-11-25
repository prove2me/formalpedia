-- Prove2me | solution 1 for GroundTheory.LocalField.norm_qpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:10.955841+00:00
-- url     : https://prove2.me/submissions/224a9c14-300c-4aa5-aa2a-4c16e86ed63f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_residueCard_pos_real

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
theorem _root_.solution (s : ℂ) : ‖(residueCard K : ℂ) ^ (-s)‖ = (residueCard K : ℝ) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos residueCard_pos_real,
    Complex.neg_re]
end GroundTheory.LocalField
