-- Prove2me | solution 1 for GlobalTheory.CompactHowe.totalDegree_substF_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:19.094472+00:00
-- url     : https://prove2.me/submissions/bb0b95e2-1968-4a30-b9b9-e43a811cde11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Theorems.Thm_GlobalTheory_CompactHowe_totalDegree_aeval_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
variable {ι : Type} {N n : ℕ}
namespace GlobalTheory.CompactHowe
theorem _root_.solution (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P
end GlobalTheory.CompactHowe
