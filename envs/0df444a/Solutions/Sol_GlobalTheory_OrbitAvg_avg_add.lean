-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:33.761474+00:00
-- url     : https://prove2.me/submissions/f3b89452-07c7-47a1-b0af-fc12392a4e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_stab_le_add
import Theorems.Thm_GlobalTheory_OrbitAvg_avgH_add
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_eq

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
theorem _root_.solution {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    avg π L (x + y) = avg π L x + avg π L y := by
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  rw [avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x),
    avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]
end GlobalTheory.OrbitAvg
