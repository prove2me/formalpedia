-- Prove2me | solution 1 for GlobalTheory.weightedRelation_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:32.303836+00:00
-- url     : https://prove2.me/submissions/5b17be01-684b-41b0-823a-93005df5264f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Theorems.Thm_GlobalTheory_eval_mem_span_pow_of_le_degree
import Theorems.Thm_GlobalTheory_exists_eval_eq_shift
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_self_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D k : ℕ) (H : MvPolynomial (Fin n) R)
    (hH : ∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β)
    (h0 : MvPolynomial.eval z H = 0) :
    (∀ β : Fin n →₀ ℕ, β.degree = k → H.coeff β ∈ Ideal.span (Set.range z)) ∧
      ∃ H' : MvPolynomial (Fin n) R,
        (∀ β, H'.coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β) ∧
        MvPolynomial.eval z H' = 0 ∧
        ∀ β : Fin n →₀ ℕ, Finsupp.weight w β = D → k + 1 ≤ β.degree → H'.coeff β = H.coeff β := by
  classical
  set Hk := MvPolynomial.homogeneousComponent k H with hHk
  have hcoeffk : ∀ β, Hk.coeff β = if β.degree = k then H.coeff β else 0 := fun β =>
    MvPolynomial.coeff_homogeneousComponent _ _ _
  have hrest : ∀ β, (H - Hk).coeff β = if β.degree = k then 0 else H.coeff β := by
    intro β
    rw [MvPolynomial.coeff_sub, hcoeffk]
    split_ifs <;> simp
  have hrest' : ∀ β, (H - Hk).coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β := by
    intro β hβ
    rw [hrest] at hβ
    split_ifs at hβ with h
    · exact absurd rfl hβ
    · have := hH β hβ
      exact ⟨by omega, this.2⟩
  have hmem : MvPolynomial.eval z Hk ∈ Ideal.span (Set.range z) ^ (k + 1) := by
    have h1 := eval_mem_span_pow_of_le_degree z (k + 1) (H - Hk) fun β hβ => (hrest' β hβ).1
    have h2 : MvPolynomial.eval z Hk = - MvPolynomial.eval z (H - Hk) := by
      rw [map_sub, h0]
      ring
    rw [h2]
    exact neg_mem h1
  have hI : ∀ β, Hk.coeff β ∈ Ideal.span (Set.range z) :=
    (isQuasiRegularSeq_self_iff z).mp hz k Hk
      (MvPolynomial.homogeneousComponent_isHomogeneous k H) hmem
  refine ⟨fun β hβ => ?_, ?_⟩
  · have := hI β
    rwa [hcoeffk, if_pos hβ] at this
  obtain ⟨G, hG, hGs⟩ := exists_eval_eq_shift z Hk hI
  have hGw : ∀ γ, G.coeff γ ≠ 0 → k + 1 ≤ γ.degree ∧ D + 1 ≤ Finsupp.weight w γ := by
    intro γ hγ
    obtain ⟨β, j, hβ, rfl⟩ := hGs γ hγ
    rw [hcoeffk] at hβ
    split_ifs at hβ with hd
    · have := hH β hβ
      have hj := hw j
      simp only [map_add, Finsupp.degree_single, Finsupp.weight_single, one_smul, hd]
      exact ⟨le_rfl, by omega⟩
    · exact absurd rfl hβ
  refine ⟨(H - Hk) + G, ?_, ?_, ?_⟩
  · intro β hβ
    rw [MvPolynomial.coeff_add] at hβ
    by_cases h1 : (H - Hk).coeff β = 0
    · rw [h1, zero_add] at hβ
      have := hGw β hβ
      exact ⟨this.1, by omega⟩
    · exact hrest' β h1
  · rw [map_add, hG, ← map_add, sub_add_cancel, h0]
  · intro β hβw hβd
    rw [MvPolynomial.coeff_add, hrest, if_neg (by omega)]
    by_cases h : G.coeff β = 0
    · rw [h, add_zero]
    · have := hGw β h
      omega
end GlobalTheory
