-- Prove2me | solution 1 for GlobalTheory.UnitCase.val_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:03.450353+00:00
-- url     : https://prove2.me/submissions/ad1ef1b7-0601-4ccd-95aa-563aae8f67f8

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
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {l : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (n : ℕ) (hn : ¬ l ∣ n) : v (n : C) = 0 := by
  induction n using induction_on_primes with
  | zero => simp at hn
  | one => simp
  | prime_mul p a hpp ih =>
    rw [Nat.cast_mul, v.map_mul, hp p hpp (by rintro rfl; exact hn (dvd_mul_right _ _)),
      ih fun h => hn (h.mul_left _), add_zero]
end GlobalTheory.UnitCase
