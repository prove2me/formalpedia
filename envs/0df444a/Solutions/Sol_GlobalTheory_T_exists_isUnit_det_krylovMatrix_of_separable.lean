-- Prove2me | solution 1 for GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:12.814728+00:00
-- url     : https://prove2.me/submissions/5550f478-c4de-40f7-9471-9c7a0d72fc7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparableStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
end _root_.GlobalTheory.T
