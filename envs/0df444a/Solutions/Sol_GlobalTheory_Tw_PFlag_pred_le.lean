-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.pred_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:51.502745+00:00
-- url     : https://prove2.me/submissions/997ae318-45b9-461b-bdf2-5dc50d7ad62f

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
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution (V : Submodule k (Fin n → k)) : F.pred V ≤ V := sSup_le fun _ h => h.2.le
end GlobalTheory.Tw.PFlag
