-- Prove2me | solution 1 for GlobalTheory.LeviDesc.Krylov.krylov_inv_mul_mul_krylov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:22.707805+00:00
-- url     : https://prove2.me/submissions/a234b7de-56f2-441a-bcf7-6d59f0d6866e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
import Theorems.Thm_GlobalTheory_LeviDesc_Krylov_mul_krylov_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LeviDesc GlobalTheory.LeviDesc.Krylov
namespace GlobalTheory.LeviDesc.Krylov
theorem _root_.solution {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
end GlobalTheory.LeviDesc.Krylov
