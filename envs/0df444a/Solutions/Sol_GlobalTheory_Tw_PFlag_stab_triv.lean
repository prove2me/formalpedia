-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.stab_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:09.492313+00:00
-- url     : https://prove2.me/submissions/27714b57-feb5-4bd2-8988-865bbccb7b01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_lieQ_triv

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
variable (F)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution : (triv n k).stab = ⊤ := eq_top_iff.2 fun _ _ => by constructor <;> simp [lieQ_triv]
end GlobalTheory.Tw.PFlag
