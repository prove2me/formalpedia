-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_eq_mul_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:40.450156+00:00
-- url     : https://prove2.me/submissions/2b3944ef-76e9-462c-bdc9-3cd69d4ae7ac

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz

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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {a c : ℂ} (ha : a ≠ 1) (h : c = a * c) : c = 0 := by
  have : (1 - a) * c = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
end GroundTheory.LocalField
