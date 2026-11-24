-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.lieQ_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:26.336713+00:00
-- url     : https://prove2.me/submissions/9aee27bc-b9b5-4625-9257-584b295220ac

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
variable {F}
variable (F)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution : (triv n k).lieQ = ⊤ := by
  refine eq_top_iff.2 fun X _ V hV v hv => ?_
  rcases hV with rfl | rfl
  · rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  · trivial
end GlobalTheory.Tw.PFlag
