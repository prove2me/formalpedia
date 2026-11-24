-- Prove2me | solution 1 for GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:39.81662+00:00
-- url     : https://prove2.me/submissions/8a636859-d84c-4569-bc6e-b20044836f2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOneStatement
import Theorems.Thm_GlobalTheory_norm_det_le_one_of_entries_le_one


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
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  first | exact @GlobalTheory.norm_det_le_one_of_entries_le_one | exact GlobalTheory.norm_det_le_one_of_entries_le_one | (intros; apply GlobalTheory.norm_det_le_one_of_entries_le_one <;> assumption)
end _root_.GlobalTheory.T
