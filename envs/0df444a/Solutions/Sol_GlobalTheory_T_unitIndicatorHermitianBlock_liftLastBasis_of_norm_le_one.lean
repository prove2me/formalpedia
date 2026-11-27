-- Prove2me | solution 1 for GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:28.09065+00:00
-- url     : https://prove2.me/submissions/4a8d88af-491e-41db-ba91-d51ac98c0a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorHermitianBlockLiftLastBasisOfNormLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement
import Theorems.Thm_GlobalTheory_JR_Step_unitU_liftH_of_norm_le_one


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
theorem _root_.solution : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  first | exact @GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | exact GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | (intros; apply GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one <;> assumption)
end _root_.GlobalTheory.T
