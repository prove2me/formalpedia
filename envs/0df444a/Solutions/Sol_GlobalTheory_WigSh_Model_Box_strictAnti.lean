-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.Box.strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:45.00118+00:00
-- url     : https://prove2.me/submissions/e3cf13e4-e525-45c0-8586-c496996c1524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model
namespace GlobalTheory.WigSh.Model
namespace Box
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) :
    StrictAnti L := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro j
  exact lt_of_lt_of_le (h j).1 (h j).2
end Box
end GlobalTheory.WigSh.Model
