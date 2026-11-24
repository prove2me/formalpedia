-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.lieN_le_lieQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:25.510988+00:00
-- url     : https://prove2.me/submissions/c564f415-9ffa-482d-b898-d3e4119c55ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_pred_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution : F.lieN ≤ F.lieQ := fun _ hX V hV v hv => F.pred_le V (hX V hV v hv)
end GlobalTheory.Tw.PFlag
