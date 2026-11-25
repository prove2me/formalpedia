-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_mainTerm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:53.960748+00:00
-- url     : https://prove2.me/submissions/f73dbd60-c7db-480d-b7f6-534b8b16ec08

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_prod_eq_monomial
import Theorems.Thm_GlobalTheory_UnitCase_sumElim_inj

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
theorem _root_.solution [Fintype κ] [DecidableEq κ] (l : ℕ) (c : C) (k : ℕ) (A B : κ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim A B) (mainTerm l c ^ k) =
      if A = l • B ∧ ∑ j, B j = k then c ^ k * Nat.multinomial Finset.univ B else 0 := by
  rw [mainTerm, smul_pow, Finset.sum_pow_eq_sum_piAntidiag, map_smul, map_sum, smul_eq_mul]
  have key : ∀ f : κ → ℕ, MvPowerSeries.coeff (Finsupp.sumElim A B)
      ((Nat.multinomial Finset.univ f : MvPowerSeries (κ ⊕ κ) C) *
        ∏ j, ((MvPowerSeries.X (Sum.inl j) : MvPowerSeries (κ ⊕ κ) C) ^ l *
          MvPowerSeries.X (Sum.inr j)) ^ (f j)) =
      if f = B then (if A = l • B then (Nat.multinomial Finset.univ B : C) else 0) else 0 := by
    intro f
    obtain ⟨f, rfl⟩ := (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).surjective f
    simp only [Finsupp.equivFunOnFinite_apply]
    rw [prod_eq_monomial, ← nsmul_eq_mul, map_nsmul, MvPowerSeries.coeff_monomial]
    by_cases h1 : f = B
    · subst h1
      by_cases h2 : A = l • f
      · subst h2
        simp [Finsupp.equivFunOnFinite]
      · rw [if_neg fun h => h2 (sumElim_inj h).1]
        simp [h2]
    · rw [if_neg fun h => h1 (sumElim_inj h).2.symm, if_neg, smul_zero]
      intro h
      exact h1 (Finsupp.ext fun j => congrFun h j)
  simp only [key]
  rw [Finset.sum_ite_eq']
  by_cases h1 : A = l • B <;> by_cases h2 : ∑ j, B j = k <;> simp [h1, h2]
end GlobalTheory.UnitCase
