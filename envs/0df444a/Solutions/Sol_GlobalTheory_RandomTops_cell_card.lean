-- Prove2me | solution 1 for GlobalTheory.RandomTops.cell_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:27.251279+00:00
-- url     : https://prove2.me/submissions/64403bce-9fc0-448c-a972-dbd6f00d13b1

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by
  unfold cell
  rw [Nat.card_Ico]
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (c + 1) * u = c * u + u by ring, ← add_assoc, Nat.add_sub_cancel_left]
end GlobalTheory.RandomTops
