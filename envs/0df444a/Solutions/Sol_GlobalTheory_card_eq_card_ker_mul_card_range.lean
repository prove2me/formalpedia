-- Prove2me | solution 1 for GlobalTheory.card_eq_card_ker_mul_card_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:46.422003+00:00
-- url     : https://prove2.me/submissions/6f92640c-19d0-48a2-b22a-3988b6208217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
end GlobalTheory
