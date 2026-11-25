-- Prove2me | solution 1 for GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:22.360424+00:00
-- url     : https://prove2.me/submissions/a5fbb0b9-5505-4fe2-91d4-c277312147cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearIndependentRatBasisAdaptedSubspace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearIndependentRatBasisAdaptedSubspaceStatement
import Theorems.Thm_GlobalTheory_adapted_basis_extension


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
theorem _root_.solution : ∀ (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)), I ≤ L → Module.finrank ℚ L = g → ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧ (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧ ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first | exact @GlobalTheory.adapted_basis_extension | exact GlobalTheory.adapted_basis_extension | (intros; apply GlobalTheory.adapted_basis_extension <;> assumption)
end _root_.GlobalTheory.T
