-- Prove2me | solution 1 for GroundTheory.LocalField.finiteExtensionStructure_valuativeExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:49.438651+00:00
-- url     : https://prove2.me/submissions/c8c738ca-926c-4691-9338-dcd6ea5a599f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Theorems.Thm_GroundTheory_LocalField_spectralNormedField_norm_algebraMap
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_vle_iff

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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    letI := (finiteExtensionStructure K L).rel
    ValuativeExtension K L := by
  let := (finiteExtensionStructure K L).rel
  constructor
  intro a b
  rw [finiteExtensionStructure_vle_iff, spectralNormedField_norm_algebraMap,
    spectralNormedField_norm_algebraMap, normedField_norm_le_norm_iff]
end GroundTheory.LocalField
