-- Prove2me | solution 1 for GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:02.414318+00:00
-- url     : https://prove2.me/submissions/25d33637-8c84-4afe-9520-533f15abca66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Theorems.Thm_GlobalTheory_etale_norm_continuous_and_zero


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Continuous A.NL ∧ A.NL 0 = 0 := by
  first | exact @GlobalTheory.etale_norm_continuous_and_zero | exact GlobalTheory.etale_norm_continuous_and_zero | (intros; apply GlobalTheory.etale_norm_continuous_and_zero <;> assumption)
end _root_.GlobalTheory.T
