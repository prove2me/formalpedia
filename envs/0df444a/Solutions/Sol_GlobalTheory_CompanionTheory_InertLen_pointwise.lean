-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:45:08.373852+00:00
-- url     : https://prove2.me/submissions/860b9cae-f632-46c0-8030-63ffeab3283c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exp_inv_mul_le
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exp_inv_mul_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_le_of_lt_exp
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_v_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_mem_int_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exists_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exists_gen
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_excess_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_entries
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_len_eq
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_hasLen_of_latLen
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution : AddVec → Dual → SpanEq → Heis → Pointwise := by
  intro hAdd hDual hSpan hHeis L instF instV ϖ σ q N hun a g₀ m hm U V C l hfrac hC u hu
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hun.2.2.2.1
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hHeis L ϖ σ q N hun).1 u hu).1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := entries hm hu
  obtain ⟨y, hyA, hy₁, hy₂, hyor⟩ :=
    exists_gen hϖ a.toNat ((C * V * mat g₀) *ᵥ colOf u) ((mat g₀ * C * U) *ᵥ colOf u)
  obtain ⟨P, ρ, hP, hρ0, hρmid, hρlast, hspan⟩ := hSpan L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u)
    (colOf u) (cornerOf u) y hϖ hfrac e1 e2 e3 e4 e5 e6 e7 e8 e9 hyA hy₁ hy₂ hyor
  have hy0 : Valued.v y ≠ 0 := by
    intro h
    rw [h] at hyA
    exact WithZero.exp_ne_zero (le_antisymm hyA zero_le')
  have hlog : ((a.toNat : ℕ) : ℤ) ≤ WithZero.log (Valued.v y) := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hy0]
    exact hyA
  obtain ⟨Y, hvy⟩ : ∃ Y : ℕ, Valued.v y = WithZero.exp (Y : ℤ) :=
    ⟨(WithZero.log (Valued.v y)).toNat, by
      rw [Int.toNat_of_nonneg (le_trans (Nat.cast_nonneg _) hlog), WithZero.exp_log hy0]⟩
  have hAY : a.toNat ≤ Y := by
    have h := hlog
    rw [hvy, WithZero.log_exp] at h
    exact_mod_cast h
  obtain ⟨e, hρe, heor⟩ := exists_bound ρ
  have hdet : Valued.v P.det = WithZero.exp (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ)) := by
    rw [hP, hC, hvy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
  have hLat := hAdd L (N + 2) P (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ)) ρ e hdet hρe heor
  rw [← hspan] at hLat
  have hHas : HasLen (mat (m * u)) ((-a).toNat + l + Y + e) := hasLen_of_latLen (by push_cast; exact hLat)
  have hlen := hHas.len_eq
  have tr : ∀ s : ℕ, (∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (s : ℤ)) ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ)) ∧
      (∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ)) := by
    intro s
    have h := hDual L ϖ σ q N hun g₀ U V C hfrac (rowOf u) (colOf u) (ϖ ^ s) hrb
    simp only [mem_int_iff hϖ] at h
    exact h
  have hY : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (Y : ℤ) :=
    (tr Y).2 ⟨fun i => (hy₁ i).trans hvy.le, fun i => (hy₂ i).trans hvy.le⟩
  have hYs : Y = a.toNat ∨ ∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp (Y : ℤ) := by
    by_cases hYA : Y = a.toNat
    · exact Or.inl hYA
    · right
      by_contra hne
      push_neg at hne
      have hlt : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ) := by
        intro j
        apply le_of_lt_exp
        have h1 : Y - 1 + 1 = Y := by omega
        rw [h1]
        exact lt_of_le_of_ne (hY j) (hne j)
      have hf := (tr (Y - 1)).1 hlt
      have hbig : WithZero.exp (Y : ℤ) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ) := by
        rcases hyor with h | ⟨i, h⟩ | ⟨i, h⟩
        · exfalso
          apply hYA
          rw [hvy] at h
          exact_mod_cast WithZero.exp_inj.1 h
        · rw [← hvy, h]
          exact hf.1 i
        · rw [← hvy, h]
          exact hf.2 i
      rw [WithZero.exp_le_exp] at hbig
      omega
  have hvρmid : ∀ j, Valued.v (ρ (mid j)) =
      (WithZero.exp (a.toNat : ℤ))⁻¹ * Valued.v (Matrix.vecMul (rowOf u) C j) := fun j => by
    rw [hρmid j, map_mul, v_pow hϖ]
  have hvρlast : Valued.v (ρ (Fin.last (N + 1))) = (WithZero.exp ((a.toNat + Y : ℕ) : ℤ))⁻¹ *
      Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) := by
    rw [hρlast, map_div₀, map_mul, v_pow hϖ, hvy, Nat.cast_add, WithZero.exp_add, mul_inv, div_eq_mul_inv,
      mul_right_comm]
  have he₁ : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun j => by
    have h := hρe (mid j)
    rw [hvρmid j] at h
    exact (exp_inv_mul_le _ _ _).1 h
  have he₂ : Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤
      WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ) := by
    have h := hρe (Fin.last (N + 1))
    rw [hvρlast] at h
    exact (exp_inv_mul_le _ _ _).1 h
  have he₃ : e = 0 ∨ (∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∨
      Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) =
        WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ) := by
    rcases heor with h | ⟨i, hi⟩
    · exact Or.inl h
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [hρ0, map_zero] at hi
        exact absurd hi.symm WithZero.exp_ne_zero
      · rw [hvρmid j] at hi
        exact Or.inr (Or.inl ⟨j, (exp_inv_mul_eq _ _ _).1 hi⟩)
      · rw [hvρlast] at hi
        exact Or.inr (Or.inr ((exp_inv_mul_eq _ _ _).1 hi))
  have hnat : a.natAbs = a.toNat + (-a).toNat := by omega
  refine ⟨by rw [hlen]; omega, fun j => ?_⟩
  rw [hlen]
  have hex := excess_iff (fun i => Valued.v (Matrix.vecMul (rowOf u) C i))
    (Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u)) a.toNat Y e j hAY hY hYs he₁ he₂ he₃
  have hsm : GlobalTheory.InertZeta.Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      ((∀ i, Valued.v (Matrix.vecMul (rowOf u) C i) ≤ WithZero.exp ((a.toNat + j / 2 : ℕ) : ℤ)) ∧
        Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤
          WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ)) := by
    unfold GlobalTheory.InertZeta.Small
    simp only [mem_int_iff hϖ]
  exact ⟨fun h => hsm.2 (hex.1 (by omega)), fun h => by have h' := hex.2 (hsm.1 h); omega⟩
end GlobalTheory.CompanionTheory.InertLen
