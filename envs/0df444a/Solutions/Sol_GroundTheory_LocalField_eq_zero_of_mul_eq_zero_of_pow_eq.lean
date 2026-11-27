-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_mul_eq_zero_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:11.696141+00:00
-- url     : https://prove2.me/submissions/a6c10c47-734b-4996-92d7-98214769d457

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_of_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution (hP : P.Monic) {b : B}
    (hb : ∀ c : B, b * c = 0 → c = 0) {y : AdjoinRoot P} {k : ℕ} (hk : k ≠ 0)
    (hy : y ^ k = AdjoinRoot.of P b) {z : AdjoinRoot P} (h : y * z = 0) : z = 0 := by
  refine eq_zero_of_of_mul_eq_zero hP hb ?_
  rw [← hy]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ, mul_assoc, h, mul_zero]
end GroundTheory.LocalField
