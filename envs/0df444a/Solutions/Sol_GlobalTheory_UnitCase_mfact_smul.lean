-- Prove2me | solution 1 for GlobalTheory.UnitCase.mfact_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:47.715451+00:00
-- url     : https://prove2.me/submissions/0bb32dc3-4504-4f4b-8919-edfca0321610

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
theorem _root_.solution [Fintype κ] {l : ℕ} (hl : l.Prime) (β : κ →₀ ℕ) :
    ∃ w : ℤ, (mfact (l • β) : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * w ∧
      (w : ZMod l) = (mfact β : ZMod l) := by
  choose z hz hz' using fun j => wilson_pow hl (β j)
  refine ⟨∏ j, z j, ?_, ?_⟩
  · rw [mfact_eq, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hz j
  · rw [mfact_eq, Nat.cast_prod, Int.cast_prod]
    exact Finset.prod_congr rfl fun j _ => hz' j
end GlobalTheory.UnitCase
