-- Prove2me | solution 1 for GlobalTheory.UnitCase.prod_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:57.945634+00:00
-- url     : https://prove2.me/submissions/4e89c3d4-c943-48a4-8ea9-7606ceb84850

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
theorem _root_.solution [Fintype κ] (l : ℕ) (B : κ →₀ ℕ) :
    ∏ j, ((MvPowerSeries.X (Sum.inl j) : MvPowerSeries (κ ⊕ κ) C) ^ l *
      MvPowerSeries.X (Sum.inr j)) ^ (B j) =
      MvPowerSeries.monomial (Finsupp.sumElim (l • B) B) 1 := by
  classical
  have : ∀ (s : Finset κ) (f : κ → (κ ⊕ κ) →₀ ℕ),
      ∏ j ∈ s, (MvPowerSeries.monomial (f j) (1 : C)) =
        MvPowerSeries.monomial (∑ j ∈ s, f j) 1 := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  simp only [mul_pow, ← pow_mul]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [this]
  congr 2
  ext (x | x)
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
end GlobalTheory.UnitCase
