-- Prove2me | solution 1 for GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:46.255087+00:00
-- url     : https://prove2.me/submissions/2fb641b4-07e8-4a7c-9722-6d33b4ec2ba2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrixStatement
import Theorems.Thm_GlobalTheory_nsmul_aeval_mem_lattice_of_intMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  first | exact @GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | exact GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | (intros; apply GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix <;> assumption)
end _root_.GlobalTheory.T
