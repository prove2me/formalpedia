-- Prove2me | solution 1 for GlobalTheory.UnitCase.mfact_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:46.448512+00:00
-- url     : https://prove2.me/submissions/c376a1a3-0be6-49c8-a220-7bd65e0a23a5

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_wilson_pow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_eq

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
theorem _root_.solution [Fintype κ] {l : ℕ} (hl : l.Prime) (A β : κ →₀ ℕ) (h : ∀ j, l * β j ≤ A j) :
    ∃ z : ℤ, (mfact A : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * z := by
  have : ∀ j, ∃ z : ℤ, ((A j).factorial : ℤ) = (-(l : ℤ)) ^ (β j) * z := by
    intro j
    obtain ⟨w, hw, -⟩ := wilson_pow hl (β j)
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (h j)
    exact ⟨w * t, by rw [ht, Nat.cast_mul, hw, mul_assoc]⟩
  choose z hz using this
  refine ⟨∏ j, z j, ?_⟩
  rw [mfact_eq, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => hz j
end GlobalTheory.UnitCase
