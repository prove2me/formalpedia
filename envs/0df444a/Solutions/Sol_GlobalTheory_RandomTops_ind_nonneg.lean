-- Prove2me | solution 1 for GlobalTheory.RandomTops.ind_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.045868+00:00
-- url     : https://prove2.me/submissions/3407ce95-2b6e-4252-9519-b909873543eb

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
theorem _root_.solution (p : Prop) : 0 ≤ ind p := by
  unfold ind
  split_ifs <;> norm_num
end GlobalTheory.RandomTops
