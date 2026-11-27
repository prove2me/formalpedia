-- Prove2me | solution 1 for GroundTheory.LocalField.localClassFieldTheory_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:02.172886+00:00
-- url     : https://prove2.me/submissions/32750f16-7504-4b90-a10d-59581a2b3f2d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalAxiom

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
open Abstract ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution : (localClassFieldTheory K Ω).val = localValuation K Ω :=
  rfl
end GroundTheory.LocalField
