-- Prove2me | solution 1 for GlobalTheory.InertZeta.mem_dosetOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:11.544745+00:00
-- url     : https://prove2.me/submissions/c25ba49a-df14-4994-a174-377062cdf153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.InertZeta
theorem _root_.solution {x y : G ⧸ K} :
    y.out ∈ DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G) ↔ dosetOf K y = dosetOf K x := by
  constructor
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h
  · intro h
    unfold dosetOf at h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K _
end GlobalTheory.InertZeta
