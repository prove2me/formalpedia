-- Prove2me | solution 1 for GlobalTheory.exists_det_one_mul_mul_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:17.953617+00:00
-- url     : https://prove2.me/submissions/b1376efb-0349-465d-94ff-fc541d01e7ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {a : ℕ}
    (A : Matrix (Fin a) (Fin a) K) :
    ∃ (P Q : Matrix (Fin a) (Fin a) K) (D : Fin a → K),
      P.det = 1 ∧ Q.det = 1 ∧ P * A * Q = Matrix.diagonal D := by
  obtain ⟨L, L', D, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  exact ⟨_, _, D, Matrix.TransvectionStruct.det_toMatrix_prod L,
    Matrix.TransvectionStruct.det_toMatrix_prod L', h⟩
end GlobalTheory
