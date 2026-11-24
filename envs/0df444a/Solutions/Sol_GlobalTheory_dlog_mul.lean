-- Prove2me | solution 1 for GlobalTheory.dlog_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:04.835845+00:00
-- url     : https://prove2.me/submissions/7b5bfa89-3731-4e41-b491-67cc9cc59f9a

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
theorem _root_.solution {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y)⁻¹ • D K F (x * y) = x⁻¹ • D K F x + y⁻¹ • D K F y := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, add_comm]
  congr 2 <;> field_simp
end GlobalTheory
