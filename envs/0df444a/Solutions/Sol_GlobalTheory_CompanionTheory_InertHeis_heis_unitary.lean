-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.heis_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:45.165475+00:00
-- url     : https://prove2.me/submissions/f194969d-fd38-45a0-886c-3173c2c6f3f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_00
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_0m
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_0l
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_middle_first_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_mm
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_ml
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_last_first_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_lm
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_ll
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
end Entries
private theorem antiJ_apply_eq_ite_rev {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if j = i.rev then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos]
    subst h
    rw [Fin.val_rev]
    omega
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    ext
    rw [Fin.val_rev]
    omega
private theorem mul_antiJ_apply_eq_apply_rev_right {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (c b : Fin n) :
    (X * antiJ L n) c b = X c b.rev := by
  rw [Matrix.mul_apply]
  have e : ∀ d : Fin n, (b = d.rev) = (d = b.rev) := fun d =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp only [antiJ_apply_eq_ite_rev, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (r b : Fin N → L) (c : L) (hb : ∀ i, b i = -σ (r i.rev))
    (hc : c + σ c = -∑ j, r j * σ (r j.rev)) :
    cT σ (heisMat r b c) * antiJ L (N + 2) * heisMat r b c = antiJ L (N + 2) := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  have hbσ : ∀ m : Fin N, σ (b m.rev) = -r m := by
    intro m
    rw [hb, Fin.rev_rev, map_neg, hσσ]
  have hσδ : ∀ p m : Fin N, σ ((1 : Matrix (Fin N) (Fin N) L) m.rev p) = (1 : Matrix (Fin N) (Fin N) L) m p.rev := by
    intro p m
    by_cases h : m = p.rev
    · subst h
      rw [Fin.rev_rev, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne (fun h' => h (by rw [← h', Fin.rev_rev])), Matrix.one_apply_ne h, map_zero]
  ext i j
  have hrow : ∀ k, (cT σ (heisMat r b c) * antiJ L (N + 2)) i k = σ (heisMat r b c k.rev i) := by
    intro k
    rw [mul_antiJ_apply_eq_apply_rev_right]
    rfl
  rw [Matrix.mul_apply]
  simp only [hrow]
  rw [sum_idx, Fin.rev_zero, Fin.rev_last, antiJ_apply_eq_ite_rev]
  simp only [← mid_rev]
  rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
  all_goals try simp only [← mid_rev, Fin.rev_zero, Fin.rev_last]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, h0]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, heis_lm, mid_ne_last q]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, heis_ll]
  · simp only [heis_lm, heis_mm, heisenberg_middle_first_zero, heis_0m, heisenberg_last_first_zero, map_zero, zero_mul, mul_zero,
      zero_add, add_zero, Finset.sum_const_zero, Fin.rev_zero]
    rw [if_neg (mid_ne_zero _).symm]
  · simp only [heis_lm, heis_mm, heis_0m, map_zero, zero_mul, mul_zero, zero_add, add_zero, hσδ p]
    simp only [mid_injective.eq_iff]
    by_cases h : q = p.rev
    · subst h
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]
  · simp only [heis_lm, heis_ml, heis_mm, heis_0m, heis_ll, heis_0l, hσδ p, map_zero, zero_mul, zero_add, mul_one]
    rw [if_neg (mid_ne_last _).symm]
    simp [Matrix.one_apply, hb, Fin.rev_rev]
  · simp [heis_ll, heis_00, heis_ml, heisenberg_middle_first_zero, heis_0l, heisenberg_last_first_zero]
  · simp only [heis_ll, heis_0m, heis_ml, heis_mm, heis_0l, heis_lm, map_one, one_mul, mul_zero,
      add_zero, hbσ, Fin.rev_last]
    rw [if_neg (mid_ne_zero _)]
    simp [Matrix.one_apply]
  · simp only [heis_ll, heis_0l, heis_ml, map_one, one_mul, mul_one, hbσ, Fin.rev_last]
    rw [if_neg last_ne_zero]
    simp only [hb, neg_mul_neg]
    linear_combination hc
end GlobalTheory.CompanionTheory.InertHeis
