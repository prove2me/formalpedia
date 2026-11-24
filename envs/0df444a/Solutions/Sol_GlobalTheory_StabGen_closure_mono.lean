-- Prove2me | solution 1 for GlobalTheory.StabGen.closure_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:14.717298+00:00
-- url     : https://prove2.me/submissions/39657d87-f5c3-4ff3-90e6-a9776cecbbd4

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded
import Theorems.Thm_GlobalTheory_StabGen_rel_le_closure
import Theorems.Thm_GlobalTheory_StabGen_subset_closure
import Theorems.Thm_GlobalTheory_StabGen_stab_closure
import Theorems.Thm_GlobalTheory_StabGen_closure_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.StabGen
open GlobalTheory.TensHead
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.StabGen
theorem _root_.solution {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))
end GlobalTheory.StabGen
