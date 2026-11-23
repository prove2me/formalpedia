-- Prove2me | solution 1 for GroundTheory.LocalField.normalizedValuation_eq_exp_ord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:38.808386+00:00
-- url     : https://prove2.me/submissions/52a87633-e46d-45e6-aa48-da06f0eb00fd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    normalizedValuation K x = WithZero.exp (-ord x) := by
  rw [ord, neg_neg, WithZero.exp_log]
  simpa using hx
end GroundTheory.LocalField
