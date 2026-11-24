-- Prove2me | solution 1 for GlobalTheory.T.lattice_real_coordinate_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:03.65098+00:00
-- url     : https://prove2.me/submissions/fb74b2dd-12d4-4709-90c7-c67f4521a3ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasisStatement
import Theorems.Thm_GlobalTheory_exists_zlattice_basis_realCoord_integral


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
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  first | exact @GlobalTheory.exists_zlattice_basis_realCoord_integral | exact GlobalTheory.exists_zlattice_basis_realCoord_integral | (intros; apply GlobalTheory.exists_zlattice_basis_realCoord_integral <;> assumption)
end _root_.GlobalTheory.T
