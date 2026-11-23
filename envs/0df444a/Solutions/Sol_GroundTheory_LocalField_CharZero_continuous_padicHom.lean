-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.continuous_padicHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:12.941878+00:00
-- url     : https://prove2.me/submissions/296099cf-b2d5-4f9e-8377-5f32d80a4f71

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero

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
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]
attribute [local instance] GroundTheory.LocalField.CharZero.uniformSpaceK
attribute [local instance] GroundTheory.LocalField.CharZero.isUniformAddGroupK
namespace GroundTheory.LocalField.CharZero
theorem _root_.solution : Continuous (padicHom K p) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)).continuous
end GroundTheory.LocalField.CharZero
