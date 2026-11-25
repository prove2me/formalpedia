-- Prove2me | solution 1 for GlobalTheory.UnitCase.val_prod_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:12.955556+00:00
-- url     : https://prove2.me/submissions/f06e7b92-d2e6-45fd-afd5-3376f276d699

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
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : l.Prime)
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ c ∈ s, f c < l) : v (∏ c ∈ s, ((f c).factorial : C)) = 0 := by
  rw [← Nat.cast_prod]
  refine val_nat hp _ ?_
  rw [Prime.dvd_finset_prod_iff hl.prime]
  rintro ⟨j, hj, hj'⟩
  exact absurd (hl.dvd_factorial.1 hj') (not_le.2 (hf j hj))
end GlobalTheory.UnitCase
