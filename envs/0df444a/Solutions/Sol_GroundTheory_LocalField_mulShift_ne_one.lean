-- Prove2me | solution 1 for GroundTheory.LocalField.mulShift_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:45.60019+00:00
-- url     : https://prove2.me/submissions/a59920ea-92a0-44b9-8d28-ad3c99b4c551

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar

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
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {a : K} (ha : a ≠ 0) : ψ.mulShift a ≠ 1 :=
  AddChar.IsPrimitive.of_ne_one hψ1 ha
end GroundTheory.LocalField
