-- Prove2me | solution 1 for GlobalTheory.RandomTops.ind_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.039206+00:00
-- url     : https://prove2.me/submissions/e79bc3ce-ebfb-4d14-8f30-07fb96b2dede

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
namespace GlobalTheory.RandomTops
theorem _root_.solution {p : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : p → 1 ≤ x) : ind p ≤ x := by
  unfold ind
  split_ifs with hp
  · exact h1 hp
  · exact h0
end GlobalTheory.RandomTops
