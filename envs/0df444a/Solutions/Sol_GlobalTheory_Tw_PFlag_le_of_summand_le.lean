-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.le_of_summand_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:06.032741+00:00
-- url     : https://prove2.me/submissions/85bd47a1-e0a4-41ed-bc02-fa0325c56cc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_pred_sup_summand

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
theorem _root_.solution {U V : Submodule ℂ (Fin n → ℂ)} (hV : V ∈ F.carrier)
    (h : ∀ V' ∈ F.carrier, V' ≤ V → F.summand V' ≤ U) : V ≤ U := by
  induction V using WellFoundedLT.induction with
  | ind V ih =>
    rw [← F.pred_sup_summand V]
    exact sup_le (sSup_le fun V' h' => ih V' h'.2 h'.1 fun V'' h1 h2 => h V'' h1 (h2.trans h'.2.le)) (h V hV le_rfl)
end GlobalTheory.Tw.PFlag
