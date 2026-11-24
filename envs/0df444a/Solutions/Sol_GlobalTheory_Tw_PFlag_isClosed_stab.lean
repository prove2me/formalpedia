-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isClosed_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:39.717536+00:00
-- url     : https://prove2.me/submissions/45da3975-4079-483d-9edc-a12e2676a012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_isClosed_lieQ

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
theorem _root_.solution : IsClosed (F.stab : Set (GL (Fin n) ℂ)) :=
  (F.isClosed_lieQ.preimage Units.continuous_val).inter (F.isClosed_lieQ.preimage Units.continuous_coe_inv)
end GlobalTheory.Tw.PFlag
