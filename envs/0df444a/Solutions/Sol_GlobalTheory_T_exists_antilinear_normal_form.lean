-- Prove2me | solution 1 for GlobalTheory.T.exists_antilinear_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:09.875948+00:00
-- url     : https://prove2.me/submissions/72fb6d6e-b8fe-4201-8a6a-f734e9762589

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAntilinearNormalForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAntilinearNormalFormStatement
import Theorems.Thm_GlobalTheory_coordsDiag


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
theorem _root_.solution : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  first | exact @GlobalTheory.coordsDiag | exact GlobalTheory.coordsDiag | (intros; apply GlobalTheory.coordsDiag <;> assumption)
end _root_.GlobalTheory.T
