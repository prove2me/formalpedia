-- Prove2me | solution 1 for GlobalTheory.RandomTops.ind_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:18.100996+00:00
-- url     : https://prove2.me/submissions/c66cfe7f-d54a-4e70-8dc9-1db76039c6f9

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
theorem _root_.solution {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  rw [if_neg h]
end GlobalTheory.RandomTops
