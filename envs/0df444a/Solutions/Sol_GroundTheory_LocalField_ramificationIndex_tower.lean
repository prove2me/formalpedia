-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.708067+00:00
-- url     : https://prove2.me/submissions/d212d49d-d825-4a91-a138-2f42f040ca49

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers

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
open ValuativeRel
variable (K L M : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Field M] [ValuativeRel M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
namespace GroundTheory.LocalField
theorem _root_.solution [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] [FiniteDimensional L M] :
    ramificationIndex K M = ramificationIndex K L * ramificationIndex L M :=
  Ideal.ramificationIdx_tower _ _
end GroundTheory.LocalField
