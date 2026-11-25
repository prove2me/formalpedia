-- Prove2me | solution 1 for GroundTheory.LocalField.finiteExtensionStructure_vle_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:29.252809+00:00
-- url     : https://prove2.me/submissions/be9b88bf-3876-46c5-9acf-a492bafbcfcb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension

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
theorem _root_.solution (x y : L) :
    letI := normedField K
    letI := spectralNormedField K L
    letI := (finiteExtensionStructure K L).rel
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl
end GroundTheory.LocalField
