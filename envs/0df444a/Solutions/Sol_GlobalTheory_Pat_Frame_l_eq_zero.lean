-- Prove2me | solution 1 for GlobalTheory.Pat.Frame.l_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:54.064943+00:00
-- url     : https://prove2.me/submissions/6a572acd-42e9-4fb0-a8bd-8ee793ca394d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt
namespace GlobalTheory.Pat
namespace Frame
theorem _root_.solution (Φ : Frame) : (Φ.l : Φ.k) = 0 := by
  have := (residue_eq_zero_iff _).2 Φ.l_mem
  rwa [map_natCast] at this
end Frame
end GlobalTheory.Pat
