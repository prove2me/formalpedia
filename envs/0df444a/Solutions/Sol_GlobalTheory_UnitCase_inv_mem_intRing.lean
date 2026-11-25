-- Prove2me | solution 1 for GlobalTheory.UnitCase.inv_mem_intRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:12.520515+00:00
-- url     : https://prove2.me/submissions/57e71d78-7788-4df5-b60b-1b83d41d8a00

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_val_nat

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
theorem _root_.solution [CharZero C] {v : AddValuation C (WithTop ℝ)} {l : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (n : ℕ) (hn : ¬ l ∣ n) :
    (n : C)⁻¹ ∈ intRing v := by
  have h0 : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at hn)
  have := v.map_mul (n : C) (n : C)⁻¹
  rw [mul_inv_cancel₀ h0, v.map_one, val_nat hp n hn, zero_add] at this
  exact this.le
end GlobalTheory.UnitCase
