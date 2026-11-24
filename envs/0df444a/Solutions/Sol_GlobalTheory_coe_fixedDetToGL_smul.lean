-- Prove2me | solution 1 for GlobalTheory.coe_fixedDetToGL_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:44.948578+00:00
-- url     : https://prove2.me/submissions/58a9adb5-f51c-437c-9c86-3e9ea9bd4c2c

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) (τ : ℍ) :
    ((fixedDetToGL hn A • τ : ℍ) : ℂ) = (A.1 0 0 * τ + A.1 0 1) / (A.1 1 0 * τ + A.1 1 1) := by
  rw [coe_smul_of_det_pos]
  · simp [num, denom, fixedDetToGL]
  · change 0 < ((Int.castRingHom ℝ).mapMatrix A.1).det
    rw [← RingHom.map_det, A.2]
    simpa using Nat.pos_of_ne_zero hn
end GlobalTheory
