-- Prove2me | solution 1 for GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:55.180495+00:00
-- url     : https://prove2.me/submissions/46582d4a-136e-44cc-afe5-ee0975eb2e28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingleton
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingletonStatement
import Theorems.Thm_GlobalTheory_JR_weilAt_of_subsingleton


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  first | exact @GlobalTheory.JR.weilAt_of_subsingleton | exact GlobalTheory.JR.weilAt_of_subsingleton | (intros; apply GlobalTheory.JR.weilAt_of_subsingleton <;> assumption)
end _root_.GlobalTheory.T
