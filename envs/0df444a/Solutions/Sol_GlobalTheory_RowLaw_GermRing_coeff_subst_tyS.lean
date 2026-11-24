-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.coeff_subst_tyS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:37.503791+00:00
-- url     : https://prove2.me/submissions/2cc2b9a6-8b5f-492c-8017-82aa54ac58e7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_coeff_pow_eq_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) {t : MvPowerSeries τ C}
    (ht : constantCoeff t = 0) (μ : τ →₀ ℕ) :
    coeff μ (PowerSeries.subst t (tyS l a)) = ∑ s ∈ Finset.range (μ.degree + 1), a s * coeff μ (t ^ (l ^ s)) := by
  have hs : PowerSeries.HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero ht
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
  · have h1 : ∀ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n (tyS l a) • coeff μ (t ^ n) =
        ∑ s ∈ Finset.range (μ.degree + 1), if l ^ s = n then a s * coeff μ (t ^ (l ^ s)) else 0 := by
      intro n hn
      by_cases h : ∃ s, l ^ s = n
      · obtain ⟨s, rfl⟩ := h
        rw [coeff_tyS_pow hl, Finset.sum_eq_single s]
        · simp
        · intro s' _ hs'
          rw [if_neg fun e => hs' (Nat.pow_right_injective hl e)]
        · intro hs'
          exfalso
          apply hs'
          have := Nat.lt_pow_self (n := s) (show 1 < l by omega)
          rw [Finset.mem_range] at hn ⊢
          omega
      · push Not at h
        rw [coeff_tyS_of_ne a n h, zero_smul]
        exact (Finset.sum_eq_zero fun s _ => if_neg (h s)).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [coeff_pow_eq_zero ht (by rw [Finset.mem_range] at h; omega), mul_zero]
  · intro n hn
    by_contra h
    apply hn
    have : μ.degree < n := by simpa using h
    simp only [coeff_pow_eq_zero ht this, smul_zero]
end GlobalTheory.RowLaw.GermRing
