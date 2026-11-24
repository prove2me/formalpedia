-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isClosed_lieQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:23.868008+00:00
-- url     : https://prove2.me/submissions/b2190ba6-8d11-4a77-a0b1-6b17ab625a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

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
theorem _root_.solution : IsClosed (F.lieQ : Set (Matrix (Fin n) (Fin n) ℂ)) := F.lieQ.closed_of_finiteDimensional
end GlobalTheory.Tw.PFlag
