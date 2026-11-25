-- Prove2me | solution 1 for GlobalTheory.T.integral_row_space_basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:51.875826+00:00
-- url     : https://prove2.me/submissions/4fb6519f-90b5-43f4-91e6-1aa1ad8e12c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralRowSpaceBasisExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralRowSpaceBasisExistsStatement
import Theorems.Thm_GlobalTheory_exists_basis_matrix_of_integral_preimage


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
theorem _root_.solution : ∀ (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k), (∀ c, Matrix.vecMul c P = 0 → c = 0) → ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  first | exact @GlobalTheory.exists_basis_matrix_of_integral_preimage | exact GlobalTheory.exists_basis_matrix_of_integral_preimage | (intros; apply GlobalTheory.exists_basis_matrix_of_integral_preimage <;> assumption)
end _root_.GlobalTheory.T
