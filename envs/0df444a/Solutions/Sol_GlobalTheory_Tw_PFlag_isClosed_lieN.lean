-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isClosed_lieN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:22.917952+00:00
-- url     : https://prove2.me/submissions/afff1c46-1a41-41f8-ada9-bc115df4d3cf

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
theorem _root_.solution : IsClosed (F.lieN : Set (Matrix (Fin n) (Fin n) ℂ)) := F.lieN.closed_of_finiteDimensional
end GlobalTheory.Tw.PFlag
