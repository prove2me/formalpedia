-- Prove2me | solution 1 for GroundTheory.LocalField.WeilGroup.coe_inertiaEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:42.031179+00:00
-- url     : https://prove2.me/submissions/a73af0d8-8354-4a69-b1aa-aaf40eb8b220

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
theorem _root_.solution (σ : inertia K Ω) :
    ((inertiaEquiv K Ω σ : (maximalUnramifiedExtension K Ω).fixingSubgroup) : Ω ≃ₐ[K] Ω) =
      toGal K Ω σ :=
  rfl
end GroundTheory.LocalField.WeilGroup
