-- Prove2me | solution 1 for GlobalTheory.RandomTops.ind_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:11.047675+00:00
-- url     : https://prove2.me/submissions/3324c399-80f8-4a96-bb74-ca6fb3fc5dd1

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
theorem _root_.solution {p q : Prop} (h : p ↔ q) : ind p = ind q := by
  rw [h]
end GlobalTheory.RandomTops
