-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.toGal_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:02.777051+00:00
-- url     : https://prove2.me/submissions/c459ba7a-14b3-4b0e-b87b-b73f857c1f8f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
open GroundTheory.LocalField.WeilGroup
variable {K Ω}
namespace GroundTheory.LocalField.WeilGroup
theorem _root_.solution (σ : WeilGroup K Ω) : toGal K Ω σ ∈ weilSubgroup K Ω := σ.2
end GroundTheory.LocalField.WeilGroup
