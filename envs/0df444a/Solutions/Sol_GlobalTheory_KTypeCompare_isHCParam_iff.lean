-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isHCParam_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:13.182019+00:00
-- url     : https://prove2.me/submissions/6fc3c659-3839-47cb-98a2-ecdb6842fa2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (μ : Fin n → ℝ) : PI.UpqRep.IsHCParam μ ↔ HarishChandraRootData.IsHCParam μ := by
  unfold PI.UpqRep.IsHCParam HarishChandraRootData.IsHCParam
  exact and_congr_right fun _ => forall_congr' fun a => exists_congr fun m => sub_eq_iff_eq_add
end GlobalTheory.KTypeCompare
