-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.summand_le_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:06.4116+00:00
-- url     : https://prove2.me/submissions/16e1063c-90d2-4cc2-b712-cb585e39f63d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_perp_anti

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
theorem _root_.solution {V V' : Submodule ℂ (Fin n → ℂ)} (hV : V ∈ F.carrier) (h : V < V') : F.summand V' ≤ perp V :=
  inf_le_right.trans (perp_anti (F.le_pred hV h))
end GlobalTheory.Tw.PFlag
