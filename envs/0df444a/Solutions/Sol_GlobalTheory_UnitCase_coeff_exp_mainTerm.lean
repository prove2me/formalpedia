-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_exp_mainTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:00.702674+00:00
-- url     : https://prove2.me/submissions/5c76b9de-4a7d-4a08-8f41-1d7617a30365

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_eq
import Theorems.Thm_GlobalTheory_UnitCase_coeff_mainTerm_pow

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
theorem _root_.solution [CharZero C] [Fintype κ] [DecidableEq κ] (l : ℕ) (c : C)
    (A B : κ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l c)) =
      if A = l • B then c ^ (∑ j, B j) * (mfact B : C)⁻¹ else 0 := by
  change ∑ k ∈ Finset.range ((Finsupp.sumElim A B).degree + 1), _ = _
  simp only [coeff_mainTerm_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (∑ j, B j)]
    · rw [if_pos ⟨h, rfl⟩, ← Nat.multinomial_spec, ← mfact_eq]
      have h1 : (Nat.multinomial Finset.univ B : C) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.multinomial_pos _ _).ne'
      push_cast
      field_simp
    · intro k _ hk
      rw [if_neg fun h' => hk h'.2.symm, zero_div]
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range, Finsupp.degree_eq_sum, Fintype.sum_sum_type]
      simp only [Finsupp.sumElim_inr]
      omega
  · simp [h]
end GlobalTheory.UnitCase
