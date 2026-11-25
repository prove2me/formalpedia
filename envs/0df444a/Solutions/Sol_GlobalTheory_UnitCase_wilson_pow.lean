-- Prove2me | solution 1 for GlobalTheory.UnitCase.wilson_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:55.904256+00:00
-- url     : https://prove2.me/submissions/4066db90-34fc-4899-8b7c-7bd9be40618f

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_asc_mod

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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (b : ℕ) :
    ∃ w : ℤ, ((l * b).factorial : ℤ) = (-(l : ℤ)) ^ b * w ∧ (w : ZMod l) = (b.factorial : ZMod l) := by
  haveI := Fact.mk hl
  induction b with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ b ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨-((b : ℤ) + 1) * ((l * b + 1).ascFactorial (l - 1) : ℕ) * w, ?_, ?_⟩
    · have e : l * (b + 1) = (l * b + (l - 1)) + 1 := by
        have := hl.one_le
        rw [mul_add]; omega
      have e2 : (l * (b + 1)).factorial =
          l * (b + 1) * ((l * b).factorial * (l * b + 1).ascFactorial (l - 1)) := by
        rw [Nat.factorial_mul_ascFactorial]
        conv_lhs => rw [e, Nat.factorial_succ, ← e]
      rw [e2, Nat.cast_mul, Nat.cast_mul ((l * b).factorial), h1]
      push_cast
      ring
    · rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, asc_mod, h2, ZMod.wilsons_lemma,
        Nat.factorial_succ]
      push_cast
      ring
end GlobalTheory.UnitCase
