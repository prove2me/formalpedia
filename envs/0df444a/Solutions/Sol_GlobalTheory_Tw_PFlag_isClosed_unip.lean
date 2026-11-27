-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isClosed_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:37.88565+00:00
-- url     : https://prove2.me/submissions/432b762f-48b0-4b10-89ee-b80e275f13ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_lieN
import Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_stab

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
variable {n : ℕ} (F : PFlag n ℂ)
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution : IsClosed (F.unip : Set (GL (Fin n) ℂ)) :=
  F.isClosed_stab.inter (F.isClosed_lieN.preimage (Units.continuous_val.sub continuous_const))
end GlobalTheory.Tw.PFlag
