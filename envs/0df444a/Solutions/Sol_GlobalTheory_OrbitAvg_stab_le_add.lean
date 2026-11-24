-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.stab_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:48.70188+00:00
-- url     : https://prove2.me/submissions/8368dcd8-018a-408c-8125-b8d615b4ba95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_mem_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution (x y : V) : stab π L x ⊓ stab π L y ≤ stab π L (x + y) := by
  intro l hl
  rw [mem_stab, map_add, (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]
end GlobalTheory.OrbitAvg
