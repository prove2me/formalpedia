-- Prove2me | solution 1 for GlobalTheory.ComplementTypes.types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:31.943599+00:00
-- url     : https://prove2.me/submissions/b0f12ad4-e89d-4d80-b31b-bd76a3acd42f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_Imports
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_equiv_of_sum_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ComplementTypes
open NumberField
open scoped ComplexConjugate
namespace GlobalTheory.ComplementTypes
namespace _root_.GlobalTheory.ComplementTypes
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q r g g' : ℕ)
    (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ)) (hty : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty)
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = (r : ℂ) * ∑ τ : E →+* ℂ, τ (H.bar a : E) + ∑ j, ty' j (a : E)) :
    r ≤ p ∧ r ≤ q ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H (p - r) (q - r) ty' := by
  classical
  let c : E →+* E := (IsCMField.complexConj E).toAlgHom.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => by simp [c]
  let t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ) := Sum.elim (fun k => k.2.comp c) ty'
  have hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E) := by
    intro a
    rw [h a, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [t, c, H.bar_eq]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum
  have key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ} := by
    intro τ
    have hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c := fun σ =>
      ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by
        simp only [he]), Fintype.card_subtype,
      Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    congr 1
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  have hconj : conj H.rt0 = -H.rt0 := by
    have hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
    · exfalso
      have hre := Complex.conj_eq_iff_re.1 h'
      have h2 := H.sqrt_neg_disc_sq
      rw [← hre] at h2
      have h3 := congrArg Complex.re h2
      simp [pow_two] at h3
      nlinarith [mul_self_nonneg H.rt0.re]
    · exact h'
  have hne : -H.rt0 ≠ H.rt0 := by
    intro h0
    have h1 : H.rt0 = 0 := by linear_combination -h0 / 2
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    have h3 := congrArg Complex.re h2
    simp at h3
    have := H.d_prime.two_le
    omega
  have hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨τ0, h0⟩
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩
  obtain ⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩
    · exact ⟨τ0, by rw [h0]; exact hne⟩
  have hp := (hty τ1).1 h1
  have hq := (hty τ2).2 h2
  have k1 := key τ1
  have k2 := key τ2
  refine ⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have := (hty τ).1 hτ
    have := key τ
    omega
  · have := (hty τ).2 hτ
    have := key τ
    omega
end _root_.GlobalTheory.ComplementTypes
end GlobalTheory.ComplementTypes
