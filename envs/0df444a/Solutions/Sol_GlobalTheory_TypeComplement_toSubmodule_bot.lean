-- Prove2me | solution 1 for GlobalTheory.TypeComplement.toSubmodule_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.419371+00:00
-- url     : https://prove2.me/submissions/739bd8bd-6ce7-46d7-b4cb-c6a144d7b11f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
namespace GlobalTheory.TypeComplement
theorem _root_.solution : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
end GlobalTheory.TypeComplement
