-- Prove2me | solution 1 for GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:56.238699+00:00
-- url     : https://prove2.me/submissions/8acbc45f-35da-4dd1-8794-9b437ecb82dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEqStatement
import Theorems.Thm_GlobalTheory_LeviDesc_Krylov_krylov_conj_eq_of_charpoly_eq


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
theorem _root_.solution : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by
  first | exact @GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | exact GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | (intros; apply GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq <;> assumption)
end _root_.GlobalTheory.T
