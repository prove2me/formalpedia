-- Prove2me | solution 1 for GroundTheory.LocalField.localClassFieldData_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:46:36.638051+00:00
-- url     : https://prove2.me/submissions/189b7424-9ceb-47bd-b0a1-93b57cb56f36

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
variable {K Ω}
variable (K Ω)
namespace GroundTheory.LocalField
theorem _root_.solution : (localClassFieldData K Ω).val = localValuation K Ω :=
  rfl
end GroundTheory.LocalField
