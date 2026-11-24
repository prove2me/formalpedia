-- Prove2me | solution 1 for GlobalTheory.LevDesc.trivMod_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:16.344003+00:00
-- url     : https://prove2.me/submissions/cb490434-4f02-440a-8d43-2b2dede2fec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_mem_trivMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}
namespace GlobalTheory.LevDesc
theorem _root_.solution : trivMod N I (I ⊔ J) = trivMod N I J := by
  ext γ
  rw [mem_trivMod, mem_trivMod, Submodule.sup_smul, smul_top_qMod, bot_sup_eq]
end GlobalTheory.LevDesc
