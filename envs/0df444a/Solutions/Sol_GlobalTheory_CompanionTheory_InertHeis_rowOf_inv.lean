-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.rowOf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:21.045708+00:00
-- url     : https://prove2.me/submissions/2e7d60c1-b65f-4ca1-9d1c-73683ca67d81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
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
private theorem antiJ_mul_apply_eq_apply_rev_left {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (a c : Fin n) :
    (antiJ L n * X) a c = X a.rev c := by
  rw [Matrix.mul_apply]
  simp only [antiJ_apply_eq_ite_rev, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private theorem mul_antiJ_apply_eq_apply_rev_right {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (c b : Fin n) :
    (X * antiJ L n) c b = X c b.rev := by
  rw [Matrix.mul_apply]
  have e : ∀ d : Fin n, (b = d.rev) = (d = b.rev) := fun d =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp only [antiJ_apply_eq_ite_rev, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private theorem antiJ_mul_antiJ_eq_one {n : ℕ} : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul_apply_eq_apply_rev_left, antiJ_apply_eq_ite_rev, Fin.rev_rev]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg (Ne.symm h), Matrix.one_apply_ne h]
private theorem mat_inv_apply_eq_sigma_mat_rev {n : ℕ} (g : GU σ n) (a b : Fin n) :
    mat g⁻¹ a b = σ (mat g b.rev a.rev) := by
  have hU : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have hinv : mat g * mat g⁻¹ = 1 := by
    show mat (g * g⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : mat g⁻¹ = antiJ L n * cT σ (mat g) * antiJ L n := by
    calc mat g⁻¹ = antiJ L n * antiJ L n * mat g⁻¹ := by rw [antiJ_mul_antiJ_eq_one, Matrix.one_mul]
      _ = antiJ L n * (cT σ (mat g) * antiJ L n * mat g * mat g⁻¹) := by rw [hU, Matrix.mul_assoc]
      _ = antiJ L n * cT σ (mat g) * antiJ L n := by
        rw [Matrix.mul_assoc (cT σ (mat g) * antiJ L n), hinv, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [key, mul_antiJ_apply_eq_apply_rev_right, antiJ_mul_apply_eq_apply_rev_left]
  rfl
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
theorem _root_.solution (u : GU σ (N + 2)) (j : Fin N) : rowOf u⁻¹ j = σ (colOf u j.rev) := by
  show mat u⁻¹ 0 (mid j) = σ (mat u (mid j.rev) (Fin.last (N + 1)))
  rw [mat_inv_apply_eq_sigma_mat_rev, mid_rev, Fin.rev_zero]
end GlobalTheory.CompanionTheory.InertHeis
