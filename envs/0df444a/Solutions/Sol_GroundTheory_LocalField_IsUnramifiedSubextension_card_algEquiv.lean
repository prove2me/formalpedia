-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramifiedSubextension.card_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:51.585664+00:00
-- url     : https://prove2.me/submissions/bfca5cfc-0e35-430d-9262-06eee176f809

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isGalois

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
namespace GroundTheory.LocalField
namespace IsUnramifiedSubextension
theorem _root_.solution {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
  have := hE.1
  have := hE.isGalois
  exact IsGalois.card_aut_eq_finrank K E
end IsUnramifiedSubextension
end GroundTheory.LocalField
