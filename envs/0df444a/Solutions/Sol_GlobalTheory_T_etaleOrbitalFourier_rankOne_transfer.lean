-- Prove2me | solution 1 for GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:10.796263+00:00
-- url     : https://prove2.me/submissions/5616d4da-6f4d-4599-9e77-8cf015e08ec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransferStatement
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_rankOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : RankOne := by
  first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)
end _root_.GlobalTheory.T
