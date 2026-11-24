-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.pred_sup_summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:27.714746+00:00
-- url     : https://prove2.me/submissions/c567540c-c77f-47ca-8668-a78d63dc4c49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_pred_le
import Theorems.Thm_GlobalTheory_Tw_sup_perp

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
variable {n : ℕ}
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : F.pred V ⊔ F.summand V = V := by
  rw [summand, inf_comm, ← sup_inf_assoc_of_le _ (F.pred_le V), sup_perp, top_inf_eq]
end GlobalTheory.Tw.PFlag
