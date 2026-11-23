-- Prove2me | solution 1 for GlobalTheory.RandomTops.tile_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:28.254147+00:00
-- url     : https://prove2.me/submissions/a652d4fb-51cd-465d-b9c3-c2a631f68220

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ico_disjoint

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
theorem _root_.solution {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  have := ico_disjoint (a := 0) (m := (6 * r + 1) * u) h
  simpa [tile] using this
end GlobalTheory.RandomTops
