-- Prove2me | solution 1 for GroundTheory.LocalField.algebraMap_integer_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:53.737416+00:00
-- url     : https://prove2.me/submissions/1f5c6dd9-40bb-486a-8226-bb2f188a5afc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface

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
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) :=
  Valuation.HasExtension.algebraMap_injective
end GroundTheory.LocalField
