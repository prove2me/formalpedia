-- Prove2me | solution 1 for GroundTheory.LocalField.selfDual_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:31:52.694945+00:00
-- url     : https://prove2.me/submissions/76f54fa4-e98f-4991-a33c-a65de1bdb8ce

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
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
namespace GroundTheory.LocalField
theorem _root_.solution (a x : Multiplicative K) : selfDual hψ hψ1 a x = ψ (a.toAdd * x.toAdd) :=
  rfl
end GroundTheory.LocalField
