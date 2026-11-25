-- Prove2me | solution 1 for GlobalTheory.relLength_sup_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:38.295176+00:00
-- url     : https://prove2.me/submissions/d6273b1c-d14e-4c89-859b-de190ead5ad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_sup_eq_add

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
theorem _root_.solution (A B C : Submodule R V) :
    relLength (A ⊔ B) C ≤ relLength A C + relLength B C := by
  rw [relLength_sup_eq_add]
  gcongr
  exact le_sup_right
end GlobalTheory
