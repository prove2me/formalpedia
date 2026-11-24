-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCorner.defect_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:55.72458+00:00
-- url     : https://prove2.me/submissions/f249e820-cf85-4d39-9ba5-7bb40651096a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_add
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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
namespace GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]
private theorem antiJ_mul_apply_eq_apply_rev_fst (M : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (antiJ L N * M) i j = M i.rev j := by
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [antiJ, Fin.val_rev]
    rw [if_pos (by omega), one_mul]
  · intro k _ hk
    simp only [antiJ]
    rw [if_neg, zero_mul]
    intro h
    apply hk
    ext
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem mul_antiJ_apply_eq_rev_col (M : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (M * antiJ L N) i j = M i j.rev := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp only [antiJ, Fin.val_rev]
    rw [if_pos (by omega), mul_one]
  · intro k _ hk
    simp only [antiJ]
    rw [if_neg, mul_zero]
    intro h
    apply hk
    ext
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem antiJ_mul_self_eq_one : antiJ L N * antiJ L N = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [antiJ_mul_apply_eq_apply_rev_fst, Matrix.one_apply]
  simp only [antiJ, Fin.val_rev]
  by_cases h : i = j
  · subst h
    rw [if_pos (by omega), if_pos rfl]
  · rw [if_neg (by intro h'; apply h; ext; omega), if_neg h]
private theorem st_eq_antiJ_mul_cT_mul_antiJ (σ : L →+* L) (A : Matrix (Fin N) (Fin N) L) :
    st σ A = antiJ L N * cT σ A * antiJ L N := by
  ext i j
  rw [mul_antiJ_apply_eq_rev_col, antiJ_mul_apply_eq_apply_rev_fst]
  simp [st, cT]
private theorem mat_mul_st_mat_eq_one {σ : L →+* L} (g : GU σ N) : mat g * st σ (mat g) = 1 := by
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hst : st σ (mat g) * mat g = 1 := by
    rw [st_eq_antiJ_mul_cT_mul_antiJ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ (mat g)), hg, antiJ_mul_self_eq_one]
  exact mul_eq_one_comm.mp hst
end GlobalTheory.CompanionTheory.InertCorner
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertCorner
theorem _root_.solution {σ : L →+* L} (g₀ : GU σ N) {U V C : Matrix (Fin N) (Fin N) L}
    (hC : (U + V * mat g₀) * C = 1) :
    -((U + V * mat g₀) * 1 * st σ (U + V * mat g₀)) + (U + V * mat g₀) * (C * V * mat g₀) * st σ (U + V * mat g₀)
      + (U + V * mat g₀) * st σ (C * V * mat g₀) * st σ (U + V * mat g₀)
      = -(U * st σ U) + V * st σ V := by
  have hg : mat g₀ * st σ (mat g₀) = 1 := mat_mul_st_mat_eq_one g₀
  have hCs : st σ C * st σ (U + V * mat g₀) = 1 := by rw [← st_mul, hC, st_one]
  have e1 : (U + V * mat g₀) * (C * V * mat g₀) = V * mat g₀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.one_mul]
  have e2 : (U + V * mat g₀) * st σ (C * V * mat g₀) * st σ (U + V * mat g₀)
      = (U + V * mat g₀) * st σ (mat g₀) * st σ V := by
    rw [st_mul, st_mul]
    simp only [Matrix.mul_assoc, hCs, Matrix.mul_one]
  have e3 : V * mat g₀ * st σ (mat g₀) * st σ V = V * st σ V := by
    rw [Matrix.mul_assoc V, hg, Matrix.mul_one]
  rw [Matrix.mul_one, e1, e2, st_add, st_mul]
  calc _ = -(U * st σ U) + V * mat g₀ * st σ (mat g₀) * st σ V := by noncomm_ring
    _ = _ := by rw [e3]
end GlobalTheory.CompanionTheory.InertCorner
