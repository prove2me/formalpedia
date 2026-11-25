-- Prove2me | solution 1 for GlobalTheory.relLength_sup_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:13.398501+00:00
-- url     : https://prove2.me/submissions/39b6f078-3a7c-4398-ac80-6ff72d094f52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_sup_le_add

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
    relLength (A ⊔ B) C ≠ ⊤ ↔ relLength A C ≠ ⊤ ∧ relLength B C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_mono_left le_sup_left C),
      ne_top_of_le_ne_top h (relLength_mono_left le_sup_right C)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_sup_le_add A B C)⟩
end GlobalTheory
