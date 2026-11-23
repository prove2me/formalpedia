-- Prove2me | solution 1 for GlobalTheory.RandomTops.cell_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:47.142891+00:00
-- url     : https://prove2.me/submissions/818feb74-36da-47f7-8e33-7dd1752a4c92

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
theorem _root_.solution {r u s c : ℕ} (hc : c ≤ 6 * r + 1) : cell r u s c ⊆ tile r u s := by
  intro x hx
  simp only [cell, tile, mem_Ico] at hx ⊢
  have : c * u ≤ (6 * r + 1) * u := Nat.mul_le_mul_right u hc
  constructor <;> nlinarith [hx.1, hx.2]
end GlobalTheory.RandomTops
