-- Prove2me | solution 1 for GlobalTheory.UnitCase.neg_pow_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:13.372464+00:00
-- url     : https://prove2.me/submissions/960ba723-62f1-4bfd-96a0-362706514928

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [CharZero C] {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (-(l : C)) ^ k * (-(l : C)⁻¹) ^ k = 1 := by
  have : (l : C) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  rw [← mul_pow, neg_mul_neg, mul_inv_cancel₀ this, one_pow]
end GlobalTheory.UnitCase
