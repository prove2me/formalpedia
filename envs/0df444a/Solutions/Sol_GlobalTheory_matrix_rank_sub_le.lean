-- Prove2me | solution 1 for GlobalTheory.matrix_rank_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:54.310793+00:00
-- url     : https://prove2.me/submissions/a61386d4-687c-4ac3-8c62-1f8652dd2917

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]
omit [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] (A B : Matrix n n K) :
    (A - B).rank ≤ A.rank + B.rank := by
  refine le_trans (Submodule.finrank_mono ?_) (Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, sub_mulVec]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ⟨x, rfl⟩)
end GlobalTheory
