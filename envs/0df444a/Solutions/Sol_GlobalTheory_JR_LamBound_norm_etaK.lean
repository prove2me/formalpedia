-- Prove2me | solution 1 for GlobalTheory.JR.LamBound.norm_etaK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:18.292937+00:00
-- url     : https://prove2.me/submissions/5f0f4302-083a-480c-a893-6fd7b573f03d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LamBound
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.LamBound
theorem _root_.solution (A : Et F E) (t : A.K) : ‖A.etaK t‖ = 1 := by
  unfold Et.etaK eta
  split_ifs <;> simp
end GlobalTheory.JR.LamBound
