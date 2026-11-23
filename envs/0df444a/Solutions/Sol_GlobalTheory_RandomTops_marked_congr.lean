-- Prove2me | solution 1 for GlobalTheory.RandomTops.marked_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:44.122885+00:00
-- url     : https://prove2.me/submissions/2febc797-457e-4a07-8fce-86fdbd4ac39d

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_cell_subset

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
theorem _root_.solution {T T' : Finset ℕ} {r u s : ℕ} (h : T ∩ tile r u s = T' ∩ tile r u s)
    (hM : Marked T r u s) : Marked T' r u s := by
  intro c hc1 hc2
  have hsub := cell_subset (r := r) (u := u) (s := s) hc2
  have e : T ∩ cell r u s c = T' ∩ cell r u s c := by
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, h]
  rw [← e]
  exact hM c hc1 hc2
end GlobalTheory.RandomTops
