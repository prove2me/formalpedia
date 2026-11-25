-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramifiedSubextension.ramificationIndex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:54.180886+00:00
-- url     : https://prove2.me/submissions/fd74daa3-75d2-4e0c-9d8e-7b6df4f01044

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence

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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
namespace IsUnramifiedSubextension
theorem _root_.solution {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : ramificationIndex K E = 1 :=
  hE.2 inferInstance inferInstance inferInstance inferInstance
end IsUnramifiedSubextension
end GroundTheory.LocalField
