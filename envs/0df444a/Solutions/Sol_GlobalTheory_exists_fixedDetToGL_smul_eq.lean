-- Prove2me | solution 1 for GlobalTheory.exists_fixedDetToGL_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:12.914949+00:00
-- url     : https://prove2.me/submissions/e3ff1ae7-526b-42d0-ada2-3baedafaf844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) : ∃ B : FixedDetMatrix (Fin 2) ℤ n,
    ∀ τ : ℍ, fixedDetToGL hn B • τ = fixedDetToGL hn A • γ • τ := by
  refine ⟨⟨A.1 * γ, by simp [A.2]⟩, fun τ ↦ ?_⟩
  have : fixedDetToGL hn ⟨A.1 * γ, by simp [A.2]⟩ = fixedDetToGL hn A * (γ : GL (Fin 2) ℝ) := by
    ext i j
    simp [fixedDetToGL, Matrix.mul_apply]
  rw [this, mul_smul]
  rfl
end GlobalTheory
