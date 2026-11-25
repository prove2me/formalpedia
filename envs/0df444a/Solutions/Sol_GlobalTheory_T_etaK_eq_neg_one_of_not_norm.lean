-- Prove2me | solution 1 for GlobalTheory.T.etaK_eq_neg_one_of_not_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:47.4639+00:00
-- url     : https://prove2.me/submissions/45e74531-9ee6-426c-9c9c-efbe6ac7d163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNormStatement
import Theorems.Thm_GlobalTheory_JR_NonNorm_etaK_eq_neg_one


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
end _root_.GlobalTheory.T
