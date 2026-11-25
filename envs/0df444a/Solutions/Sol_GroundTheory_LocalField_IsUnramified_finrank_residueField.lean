-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramified.finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:55.310307+00:00
-- url     : https://prove2.me/submissions/2922e120-c0a6-4a47-a03e-5b12728a4f4f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff_finrank_residueField

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
namespace IsUnramified
theorem _root_.solution [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance
end IsUnramified
end GroundTheory.LocalField
