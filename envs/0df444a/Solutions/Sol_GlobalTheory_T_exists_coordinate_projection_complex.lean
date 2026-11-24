-- Prove2me | solution 1 for GlobalTheory.T.exists_coordinate_projection_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:48.829344+00:00
-- url     : https://prove2.me/submissions/41fbb098-00a5-4ee5-9e23-23a2285b4b00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoordinateProjectionComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoordinateProjectionComplexStatement
import Theorems.Thm_GlobalTheory_realDiag_conj_coordProj


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
theorem _root_.solution : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  first | exact @GlobalTheory.realDiag_conj_coordProj | exact GlobalTheory.realDiag_conj_coordProj | (intros; apply GlobalTheory.realDiag_conj_coordProj <;> assumption)
end _root_.GlobalTheory.T
