-- Prove2me | solution 1 for GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:27.435002+00:00
-- url     : https://prove2.me/submissions/0c86fdd0-47d5-421b-9ae8-66b103ff1e29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoordsEqPairingsRationalSymplecticBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoordsEqPairingsRationalSymplecticBasisStatement
import Theorems.Thm_GlobalTheory_coords_in_rational_symplectic_basis


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
theorem _root_.solution : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) → (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  first | exact @GlobalTheory.coords_in_rational_symplectic_basis | exact GlobalTheory.coords_in_rational_symplectic_basis | (intros; apply GlobalTheory.coords_in_rational_symplectic_basis <;> assumption)
end _root_.GlobalTheory.T
