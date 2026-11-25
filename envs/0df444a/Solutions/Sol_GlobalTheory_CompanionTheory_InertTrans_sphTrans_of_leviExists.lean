-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:35.038095+00:00
-- url     : https://prove2.me/submissions/8a87c138-0535-40f9-bdcd-16a753112245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_conj_mem_radU
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_isUnipU_of_radQ
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_borel
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_mem_K
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_eq_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_P_fIwasawa_iwasawa
import Theorems.Thm_Formalism_UG_P_fSatake_borel_diag_mul
import Theorems.Thm_Formalism_UG_P_fSatake_borel_mul
import Theorems.Thm_Formalism_UG_P_fSatake_ord_zpow
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution : LeviExists → SphTrans := by
  intro hL L _ _ ϖ σ q N r hU hr α φ φ₀ hα hφ h1 hφ₀ h01 a g₀ m hm u hu
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have e := levi_eq_mul hmb hmk hm
  have hkK : mk ∈ KU σ (N + 2) := levi_mem_K hU.2.1 hmk hk₀
  have hmbB : IsBorelU mb := levi_borel hmb hb₀
  have hu' : mk * u * mk⁻¹ ∈ radQ σ N := conj_mem_radU hmk.1 hu
  have hu'B := isUnipU_of_radQ hu'
  have e2 : m * u = (mb * (mk * u * mk⁻¹)) * 1 * mk := by rw [e]; group
  have d : ∀ (i : Fin (N + 2)) (x : L), mat mb i i = x →
      (((mb * (mk * u * mk⁻¹) : GU σ (N + 2)) : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i i = x := by
    intro i x hx
    have := P.fSatake_borel_diag_mul hmbB hu'B.1 i
    rw [hu'B.2, mul_one] at this
    exact this.trans hx
  have e3 : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hφ₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h01, mul_one] at this
  rw [e2, hφ _ _ _ (P.fSatake_borel_mul hmbB hu'B.1) hkK, h1, mul_one, e3]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : ((0 : Fin (r + 1)) : ℕ) < N + 2 := by simp
    rw [dif_pos h0]
    have e0 : (⟨((0 : Fin (r + 1)) : ℕ), h0⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0, d _ _ hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    push_cast
    simp only [Fin.val_zero]
    congr 3
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.val < N := by have := i.2; omega
    have hi' : (i.succ : Fin (r + 1)).val < N + 2 := by simp; omega
    rw [dif_pos hi, dif_pos hi']
    have ei : (⟨(i.succ : Fin (r + 1)).val, hi'⟩ : Fin (N + 2)) = mid ⟨i.val, hi⟩ := by
      ext; simp
    rw [ei, d _ _ (hmb.2.2.2 ⟨i.val, hi⟩ ⟨i.val, hi⟩)]
    have ex : ((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ : Fin (r + 1)).val : ℤ) = (N : ℤ) - 1 - 2 * (i.val : ℤ) := by
      simp; ring
    rw [ex]
    rfl
end GlobalTheory.CompanionTheory.InertTrans
