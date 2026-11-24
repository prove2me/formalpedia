-- Prove2me | solution 1 for GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:28.125099+00:00
-- url     : https://prove2.me/submissions/2e1aebe4-3539-4049-81a0-c28b7ea7080c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NsmulAevalMemLatticeOfIntRationalMatrix
import Theorems.Thm_GlobalTheory_nsmul_aeval_mem_lattice_of_intMatrix_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ :=
  fun g n Λ e hΛ γ Tq hT p D hD => nsmul_aeval_mem_lattice_of_intMatrix_basis g n Λ e hΛ γ Tq hT p D hD
end GlobalTheory
