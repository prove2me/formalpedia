-- Prove2me | solution 1 for GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:25.705789+00:00
-- url     : https://prove2.me/submissions/b554c986-91fc-409e-9a5c-272c6c3d3503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianEndoMatrixRationalInLatticeBasisStatement
import Theorems.Thm_GlobalTheory_herm_endo_matrix_rat


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
theorem _root_.solution : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  first | exact @GlobalTheory.herm_endo_matrix_rat | exact GlobalTheory.herm_endo_matrix_rat | (intros; apply GlobalTheory.herm_endo_matrix_rat <;> assumption)
end _root_.GlobalTheory.T
