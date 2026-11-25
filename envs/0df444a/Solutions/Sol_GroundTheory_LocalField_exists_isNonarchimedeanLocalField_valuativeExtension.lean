-- Prove2me | solution 1 for GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:42.308631+00:00
-- url     : https://prove2.me/submissions/eb097d45-fbb6-474c-a977-b2ab18219bc7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_valuativeExtension
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_isNonarchimedeanLocalField

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
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension K L :=
  ⟨(finiteExtensionStructure K L).rel, (finiteExtensionStructure K L).top,
    finiteExtensionStructure_isNonarchimedeanLocalField K L,
    finiteExtensionStructure_valuativeExtension K L⟩
end GroundTheory.LocalField
