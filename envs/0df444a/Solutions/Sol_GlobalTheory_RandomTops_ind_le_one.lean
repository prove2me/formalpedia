-- Prove2me | solution 1 for GlobalTheory.RandomTops.ind_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.895452+00:00
-- url     : https://prove2.me/submissions/5939834a-c884-4962-93e0-ff4219a91f8f

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
theorem _root_.solution (p : Prop) : ind p ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num
end GlobalTheory.RandomTops
