-- Prove2me | solution 1 for GroundTheory.LocalField.ord_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:02.537805+00:00
-- url     : https://prove2.me/submissions/25d8ca03-10df-41df-9a86-a9202722b015

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
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord (x * y) = ord x + ord y := by
  simp [ord, WithZero.log_mul, hx, hy]; ring
end GroundTheory.LocalField
