-- Prove2me | solution 1 for GlobalTheory.dlog_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:05.572795+00:00
-- url     : https://prove2.me/submissions/7d7d642c-9427-43d7-87c0-47284a5d6938

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
namespace GlobalTheory
theorem _root_.solution {x : F} (hx : x ≠ 0) (m : ℤ) :
    (x ^ m)⁻¹ • D K F (x ^ m) = m • x⁻¹ • D K F x := by
  rw [Derivation.leibniz_zpow, smul_comm, smul_smul]
  congr 2
  rw [zpow_sub_one₀ hx, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero m hx), one_mul]
end GlobalTheory
