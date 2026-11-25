-- Prove2me | solution 1 for GlobalTheory.T.hermitian_form_change_of_basis_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:31.497358+00:00
-- url     : https://prove2.me/submissions/df4e1d73-bfeb-4a02-83d7-5bb15535d691

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntries
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntriesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IsometricMatrix_main


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
theorem _root_.solution : ∀ {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ) (J : Matrix (Fin n) (Fin n') ℂ),
    Hᴴ = H → H'ᴴ = H' → IsUnit H.det → IsUnit H'.det → Jᴴ * H * J = H' →
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  first | exact @GlobalTheory.CompanionTheory.IsometricMatrix.main | exact GlobalTheory.CompanionTheory.IsometricMatrix.main | (intros; apply GlobalTheory.CompanionTheory.IsometricMatrix.main <;> assumption)
end _root_.GlobalTheory.T
