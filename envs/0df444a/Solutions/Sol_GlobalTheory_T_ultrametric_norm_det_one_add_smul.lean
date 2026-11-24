-- Prove2me | solution 1 for GlobalTheory.T.ultrametric_norm_det_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:31.565515+00:00
-- url     : https://prove2.me/submissions/eed228cb-cc67-40c7-9991-fef9d6ebed95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Theorems.Thm_GlobalTheory_UnitDiscAlg_norm_det_one_add_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → (∀ i j, ‖x i j‖ ≤ 1) → ‖(1 + ϖ • x).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | exact GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | (intros; apply GlobalTheory.UnitDiscAlg.norm_det_one_add_smul <;> assumption)
end _root_.GlobalTheory.T
