-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.iSup_summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:34.822657+00:00
-- url     : https://prove2.me/submissions/6dc4c525-219e-42ed-be5d-5ec7b6cf01dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_le_of_summand_le

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
theorem _root_.solution (F : PFlag n ℂ) : ⨆ V ∈ F.carrier, F.summand V = ⊤ :=
  top_le_iff.1 (le_of_summand_le F.top_mem fun V hV _ => le_iSup₂_of_le V hV le_rfl)
end GlobalTheory.Tw.PFlag
