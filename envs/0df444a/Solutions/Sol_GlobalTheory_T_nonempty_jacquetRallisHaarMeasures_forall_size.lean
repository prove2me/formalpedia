-- Prove2me | solution 1 for GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:17.337801+00:00
-- url     : https://prove2.me/submissions/0e2883ce-44d6-4a51-8fa3-fd3b32923472

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSizeStatement
import Theorems.Thm_GlobalTheory_JR_HaarExist_meas_nonempty


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  first | exact @GlobalTheory.JR.HaarExist.meas_nonempty | exact GlobalTheory.JR.HaarExist.meas_nonempty | (intros; apply GlobalTheory.JR.HaarExist.meas_nonempty <;> assumption)
end _root_.GlobalTheory.T
