-- Prove2me | solution 1 for GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:38.716365+00:00
-- url     : https://prove2.me/submissions/bcc0fdf6-8968-44b3-bb2a-487f103c5dfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMoment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement
import Theorems.Thm_GlobalTheory_JR_BigMoment_matchAt_unit_of_one_lt_norm


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | exact GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | (intros; apply GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm <;> assumption)
end _root_.GlobalTheory.T
