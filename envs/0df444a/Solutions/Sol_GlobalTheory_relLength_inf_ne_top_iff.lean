-- Prove2me | solution 1 for GlobalTheory.relLength_inf_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:01.229176+00:00
-- url     : https://prove2.me/submissions/1abd06b5-3c8c-4117-b7a2-96cd239b44bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_inf_le_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution {A B C : Submodule R V} :
    relLength A (B ⊓ C) ≠ ⊤ ↔ relLength A B ≠ ⊤ ∧ relLength A C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_anti_right A inf_le_left),
      ne_top_of_le_ne_top h (relLength_anti_right A inf_le_right)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_inf_le_add A B C)⟩
end GlobalTheory
