-- Prove2me | solution 1 for GlobalTheory.adicCompletion_val_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:21.25925+00:00
-- url     : https://prove2.me/submissions/76d8b0ed-dcbf-4325-bd97-7dda29192c04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl
end GlobalTheory
