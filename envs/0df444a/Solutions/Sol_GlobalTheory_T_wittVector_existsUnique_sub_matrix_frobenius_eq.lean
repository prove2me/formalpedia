-- Prove2me | solution 1 for GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:44.978083+00:00
-- url     : https://prove2.me/submissions/0d2fa7df-75e5-40c1-ab1c-bf99349620c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEqStatement
import Theorems.Thm_GlobalTheory_wittSolve_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  first | exact @GlobalTheory.wittSolve_unique | exact GlobalTheory.wittSolve_unique | (intros; apply GlobalTheory.wittSolve_unique <;> assumption)
end _root_.GlobalTheory.T
