-- Prove2me | solution 1 for GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:25:06.710134+00:00
-- url     : https://prove2.me/submissions/16c6e1e0-bede-4e14-9a37-1d9fbdc28dab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalMinorsMatrixMemUnitaryGroupStatement
import Theorems.Thm_GlobalTheory_IsLogBounded_det
import Theorems.Thm_GlobalTheory_minorsMatrix_mem_unitaryGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  first | exact @GlobalTheory.minorsMatrix_mem_unitaryGroup | exact GlobalTheory.minorsMatrix_mem_unitaryGroup | (intros; apply GlobalTheory.minorsMatrix_mem_unitaryGroup <;> assumption)
end _root_.GlobalTheory.T
