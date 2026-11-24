-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.stab_le_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:49.534682+00:00
-- url     : https://prove2.me/submissions/75e4c22a-d705-4492-9547-2a261b2a263d

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
theorem _root_.solution (c : ℂ) (x : V) : stab π L x ≤ stab π L (c • x) := by
  intro l hl
  rw [mem_stab, map_smul, (mem_stab π L).mp hl]
end GlobalTheory.OrbitAvg
