-- Prove2me | solution 1 for GlobalTheory.T.exists_theta_division_point_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:15.213583+00:00
-- url     : https://prove2.me/submissions/1b83b90d-1f09-4987-8def-05d34f7658b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_exists_division_point_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | exact GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero <;> assumption)
end _root_.GlobalTheory.T
