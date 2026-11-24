-- Prove2me | solution 1 for GlobalTheory.zarhinAction_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:39.706456+00:00
-- url     : https://prove2.me/submissions/54546239-faec-4080-81bd-b7c25b49d9ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
open GlobalTheory
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (ρ0 : R →+* Matrix n n ℤ) (B A : Matrix n n ℤ) (x : Matrix q q ℤ)
    (hB : ∀ a, (ρ0 a)ᵀ * B = B * ρ0 (σ a)) (hA : ∀ a, ρ0 (σ a) * A = A * (ρ0 a)ᵀ) (a : R) :
    (zarhinAction (q := q) σ ρ0 a)ᵀ *
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) =
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) * zarhinAction (q := q) σ ρ0 (σ a) := by
  simp only [zarhinAction, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, fromBlocks_transpose,
    fromBlocks_multiply, ← kroneckerMap_transpose, transpose_transpose, transpose_one,
    transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hσ]
  simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA, hB]
end GlobalTheory
