-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:40:56.678167+00:00
-- url     : https://prove2.me/submissions/2b611e3f-086e-47a6-979c-b8bc96d9cb30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_st_one
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_vecMul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_add
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_isInt_st
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_H_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_defect_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_exists_trace_one
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertCorner
theorem _root_.solution : Heis → Dual → SmallCorner := by
  intro hH _hDl L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  obtain ⟨h1, -, h3⟩ := hH L ϖ σ q N hU
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.InertZeta.exists_trace_one hU
  obtain ⟨hσ, hv, hϖ, hϖv, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, -, -, hWC⟩ := hF
  have hCW : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hWC
  have hrW : r = (r ᵥ* C) ᵥ* (U + V * mat g₀) := by
    rw [Matrix.vecMul_vecMul, hCW, Matrix.vecMul_one]
  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : L, w = r ⬝ᵥ ((C * V * mat g₀) *ᵥ b) := ⟨_, rfl⟩
  obtain ⟨xx, hxx⟩ : ∃ xx : L, xx = r ⬝ᵥ b - w - σ w := ⟨_, rfl⟩
  have hb' : b = -(dv σ r) := by
    rw [hb]
    ext i
    simp [dv]
  have e1 : r ⬝ᵥ b = -(H σ r 1 r) := by
    unfold H
    rw [hb', Matrix.one_mulVec, dotProduct_neg]
  have e2 : w = -(H σ r (C * V * mat g₀) r) := by
    unfold H
    rw [hw, hb', Matrix.mulVec_neg, dotProduct_neg]
  have e3 : σ w = -(H σ r (st σ (C * V * mat g₀)) r) := by
    rw [e2, map_neg, H_conj σ hσ]
  have key : xx = H σ (r ᵥ* C) (-(U * st σ U) + V * st σ V) (r ᵥ* C) := by
    rw [hxx, e1, e3, e2, ← defect_eq g₀ hWC, H_add, H_add, H_neg, ← H_vecMul, ← H_vecMul, ← H_vecMul, ← hrW]
    ring
  have hM : GlobalTheory.InertZeta.IsInt (-(U * st σ U) + V * st σ V) := by
    refine GlobalTheory.InertZeta.IsInt.add ?_ (GlobalTheory.InertZeta.IsInt.mul hVi (isInt_st hv hVi))
    intro i j
    rw [Matrix.neg_apply]
    exact Subring.neg_mem _ (GlobalTheory.InertZeta.IsInt.mul hUi (isInt_st hv hUi) i j)
  have hint : ϖ ^ (2 * e) * xx ∈ intL L := by
    have ht : σ (ϖ ^ e) = ϖ ^ e := by rw [map_pow, hϖ]
    have h2 : ϖ ^ (2 * e) * xx
        = H σ (ϖ ^ e • (r ᵥ* C)) (-(U * st σ U) + V * st σ V) (ϖ ^ e • (r ᵥ* C)) := by
      rw [H_smul σ _ _ ht, key, two_mul, pow_add]
    rw [h2]
    refine H_mem hv hM (fun j => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hr j
  have hϖint : ϖ ∈ intL L := by
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff]
    rw [hϖv, ← WithZero.coe_one, WithZero.coe_le_coe]
    exact (Multiplicative.ofAdd_le (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)
  have hσxx : σ xx = xx := by
    rw [hxx, map_sub, map_sub, hσ, e1, map_neg, H_conj σ hσ, st_one]
    ring
  have hsum : r ⬝ᵥ b = -∑ j, r j * σ (r j.rev) := by
    rw [hb]
    simp [dotProduct, Finset.sum_neg_distrib]
  have hc : (w + xx * τ) + σ (w + xx * τ) = -∑ j, r j * σ (r j.rev) := by
    rw [← hsum, map_add, map_mul, hσxx]
    have hrb : r ⬝ᵥ b = xx + w + σ w := by rw [hxx]; ring
    rw [hrb]
    linear_combination xx * hτ1
  obtain ⟨u, hu, hrow, hcorner⟩ := h3 r (w + xx * τ) hc
  obtain ⟨hrc, -, -⟩ := h1 u hu
  have hcol : colOf u = b := by
    funext i
    have h := hrc i.rev
    rw [Fin.rev_rev, hrow] at h
    rw [hb]
    calc colOf u i = σ (σ (colOf u i)) := (hσ _).symm
      _ = σ (-(r i.rev)) := by rw [h, neg_neg]
      _ = -σ (r i.rev) := map_neg _ _
  refine ⟨u, hu, hrow, ?_⟩
  unfold GlobalTheory.InertZeta.Small
  refine ⟨?_, ?_⟩
  · rw [hrow]
    exact hr
  · rw [hcorner, hrow, hcol, ← hw]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hef
    rw [show w + xx * τ - w = xx * τ by ring, pow_add,
      show ϖ ^ (2 * e) * ϖ ^ d * (xx * τ) = (ϖ ^ (2 * e) * xx) * (ϖ ^ d * τ) by ring]
    exact Subring.mul_mem _ hint (Subring.mul_mem _ (Subring.pow_mem _ hϖint d) hτ)
end GlobalTheory.CompanionTheory.InertCorner
