-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.topRows_eMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:36.550879+00:00
-- url     : https://prove2.me/submissions/1546cfb6-e654-4491-8221-a5909ef08dc2

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_topRows_eMat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet.TestNearE
theorem _root_.solution (r t : ℕ) : topRows r t (eMat k r t) = 1 := by
  simpa using topRows_eMat_mul (k := k) r t 1
end GlobalTheory.GodementJacquet.TestNearE
