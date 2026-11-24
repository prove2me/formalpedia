-- Prove2me | solution 1 for GlobalTheory.perpVector_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:10.882095+00:00
-- url     : https://prove2.me/submissions/879ae698-8acc-402f-ac71-028a19b474b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (ε : ι → Module.Dual R M) (e' : ι → M) {g : M}
    (hg : ∀ a, ε a g = 0) : perpVector ε e' g = (pairingMatrix ε e').det • g := by
  simp [perpVector, hg]
end GlobalTheory
