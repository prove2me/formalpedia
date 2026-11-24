-- Prove2me | solution 1 for GlobalTheory.fixedDetToGL_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:20.05945+00:00
-- url     : https://prove2.me/submissions/e8701b64-927a-4ada-a953-edd1e19452d2

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (γ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n)
    (τ : ℍ) : fixedDetToGL hn (γ • A) • τ = γ • fixedDetToGL hn A • τ := by
  have : fixedDetToGL hn (γ • A) = (γ : GL (Fin 2) ℝ) * fixedDetToGL hn A := by
    ext i j
    simp [fixedDetToGL, FixedDetMatrices.smul_coe, Matrix.mul_apply]
  rw [this, mul_smul]
  rfl
end GlobalTheory
