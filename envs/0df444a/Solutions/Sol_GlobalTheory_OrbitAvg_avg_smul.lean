-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avg_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:34.843665+00:00
-- url     : https://prove2.me/submissions/73864734-7f04-4bdf-8d59-19b3c8214446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_stab_le_smul
import Theorems.Thm_GlobalTheory_OrbitAvg_avgH_smul
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
theorem _root_.solution {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by
  rw [avg_eq π L (stab_le_smul π L c x), avgH_smul]
  rfl
end GlobalTheory.OrbitAvg
