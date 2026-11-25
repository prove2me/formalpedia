-- Prove2me | solution 1 for GlobalTheory.UnitCase.asc_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:55.93661+00:00
-- url     : https://prove2.me/submissions/381e9a9e-e77b-4390-b791-4ca2c5f4b01a

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
theorem _root_.solution (l b k : ℕ) :
    (((l * b + 1).ascFactorial k : ℕ) : ZMod l) = (k.factorial : ZMod l) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.ascFactorial_succ, Nat.factorial_succ, Nat.cast_mul, ih]
    simp [add_comm]
end GlobalTheory.UnitCase
