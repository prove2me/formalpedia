-- Prove2me | solution 1 for MatroidEquitability.proof_theorem_2_eq_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:47.813067+00:00
-- url     : https://prove2.me/submissions/2933caf1-888e-4b0c-b232-83ffeb2b8004

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_dualVector
import Definitions.Def_MatroidEquitability_supportPlus

section
set_option autoImplicit false

namespace MatroidEquitability
namespace Dev.Eq6

open Finset

lemma setWeight_eq_sum {α : Type*} {E : Set α} (hE : E.Finite) {A : Set α} (hA : A ⊆ E)
    (f : α → ℝ) : setWeight f A = ∑ e ∈ hE.toFinset, A.indicator f e := by
  unfold setWeight
  rw [finsum_mem_def]
  apply finsum_eq_sum_of_support_subset
  intro e he
  have h1 : e ∈ A := Set.support_indicator_subset he
  simpa using hA h1

lemma setWeight_E {α : Type*} {E : Set α} (hE : E.Finite) (f : α → ℝ) :
    setWeight f E = ∑ e ∈ hE.toFinset, f e := by
  unfold setWeight
  exact finsum_mem_eq_finite_toFinset_sum f hE

lemma indicator_eq {α : Type*} (A : Set α) (f : α → ℝ) (e : α) :
    A.indicator f e = f e * A.indicator (1 : α → ℝ) e := by
  by_cases h : e ∈ A <;> simp [h]

lemma setWeight_sub {α : Type*} {E : Set α} (hE : E.Finite) {B D : Set α} (hB : B ⊆ E)
    (hD : D ⊆ E) (u : α → ℝ) :
    setWeight u B - setWeight u D =
      ∑ e ∈ hE.toFinset, u e * (B.indicator (1 : α → ℝ) e - D.indicator (1 : α → ℝ) e) := by
  rw [setWeight_eq_sum hE hB, setWeight_eq_sum hE hD, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [indicator_eq B, indicator_eq D]; ring

lemma weak_sum {α : Type*} {E : Set α} (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ)
    (lam : Set α → Set α → ℝ) :
    ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) =
      ∑ e ∈ hE.toFinset, u e * dualVector Fp Fm lam e := by
  have h1 : ∀ B ∈ Fp, ∀ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) =
      ∑ e ∈ hE.toFinset, u e * (lam B D * (B.indicator (1 : α → ℝ) e - D.indicator (1 : α → ℝ) e)) := by
    intro B hB D hD
    rw [setWeight_sub hE (hFpE B hB) (hFmE D hD), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [Finset.sum_congr rfl (fun B hB => Finset.sum_congr rfl (fun D hD => h1 B hB D hD))]
  unfold dualVector
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun B _ => Finset.sum_comm)]
  exact Finset.sum_comm



lemma setWeight_indicator_ncard {α : Type*} {E : Set α} (hE : E.Finite) {B S : Set α}
    (hB : B ⊆ E) (hS : S ⊆ E) :
    setWeight (S.indicator (1 : α → ℝ)) B = ((B ∩ S).ncard : ℝ) := by
  classical
  rw [setWeight_eq_sum hE hB]
  have h1 : ∀ e, B.indicator (S.indicator (1 : α → ℝ)) e = if e ∈ B ∩ S then 1 else 0 := by
    intro e
    by_cases h1 : e ∈ B <;> by_cases h2 : e ∈ S <;> simp [h1, h2]
  simp_rw [h1]
  rw [Finset.sum_boole]
  have : B ∩ S = ↑(hE.toFinset.filter (· ∈ B ∩ S)) := by
    ext e
    simp only [Set.mem_inter_iff, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨hB h.1, h⟩
    · intro h; exact h.2
  have h2 : (B ∩ S).ncard = (hE.toFinset.filter (· ∈ B ∩ S)).card := by
    rw [← Set.ncard_coe_finset, ← this]
  rw [h2]

lemma sum_support {α : Type*} (Fp Fm : Finset (Set α)) (lam : Set α → Set α → ℝ)
    (g : Set α → Set α → ℝ) (hg : ∀ B ∈ Fp, ∀ D ∈ Fm, ¬ 0 < lam B D → g B D = 0) :
    ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam, g B D =
      ∑ B ∈ Fp, ∑ D ∈ Fm, g B D := by
  classical
  have hsub1 : supportPlus Fp Fm lam ⊆ Fp := Finset.filter_subset _ _
  have hsub2 : supportMinus Fp Fm lam ⊆ Fm := Finset.filter_subset _ _
  rw [Finset.sum_subset hsub1]
  · apply Finset.sum_congr rfl
    intro B hB
    apply Finset.sum_subset hsub2
    intro D hD hDn
    apply hg B hB D hD
    intro hpos
    apply hDn
    simp only [supportMinus, Finset.mem_filter]
    exact ⟨hD, B, hB, hpos⟩
  · intro B hB hBn
    apply Finset.sum_eq_zero
    intro D hD
    apply hg B hB D (hsub2 hD)
    intro hpos
    apply hBn
    have hD2 := hsub2 hD
    simp only [supportPlus, Finset.mem_filter]
    exact ⟨hB, D, hD2, hpos⟩

end Dev.Eq6

theorem chk_proof_theorem_2_eq_6 {α : Type*} (E : Set α) (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ) (γ : ℝ)
    (lam : Set α → Set α → ℝ) (hu : ∀ e ∈ E, 0 ≤ u e ∧ u e ≤ 1)
    (hlam : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D) (hsum : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1)
    (hslack : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 < lam B D → setWeight u B - setWeight u D = γ)
    (h5 : ∀ e ∈ E,
      (u e = 0 → dualVector Fp Fm lam e ≤ 0) ∧
      (0 < u e → u e < 1 → dualVector Fp Fm lam e = 0) ∧
      (u e = 1 → 0 ≤ dualVector Fp Fm lam e))
    (S : Set α) (hS : S = {e ∈ E | u e = 1}) :
    γ = ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (setWeight u B - setWeight u D) ∧
    ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (setWeight u B - setWeight u D) =
      setWeight (fun e => u e * dualVector Fp Fm lam e) E ∧
    setWeight (fun e => u e * dualVector Fp Fm lam e) E = setWeight (dualVector Fp Fm lam) S ∧
    setWeight (dualVector Fp Fm lam) S =
      ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (((B ∩ S).ncard : ℝ) - ((D ∩ S).ncard : ℝ)) := by
  classical
  have hSE : S ⊆ E := by rw [hS]; intro e he; exact he.1
  have hA : ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (setWeight u B - setWeight u D) =
      ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) := by
    apply Dev.Eq6.sum_support
    intro B hB D hD hn
    have : lam B D = 0 := le_antisymm (not_lt.1 hn) (hlam B hB D hD)
    rw [this]; ring
  have hB : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) = γ := by
    have : ∀ B ∈ Fp, ∀ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) = lam B D * γ := by
      intro B hB D hD
      rcases (hlam B hB D hD).eq_or_lt with h | h
      · rw [← h]; ring
      · rw [hslack B hB D hD h]
    rw [Finset.sum_congr rfl (fun B hB => Finset.sum_congr rfl (fun D hD => this B hB D hD))]
    simp_rw [← Finset.sum_mul, hsum]; ring
  have hC : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (setWeight u B - setWeight u D) =
      setWeight (fun e => u e * dualVector Fp Fm lam e) E := by
    rw [Dev.Eq6.weak_sum hE Fp Fm hFpE hFmE u lam, Dev.Eq6.setWeight_E hE]
  have hD : setWeight (fun e => u e * dualVector Fp Fm lam e) E =
      setWeight (dualVector Fp Fm lam) S := by
    rw [Dev.Eq6.setWeight_E hE, Dev.Eq6.setWeight_eq_sum hE hSE]
    apply Finset.sum_congr rfl
    intro e he
    have he' := hE.mem_toFinset.1 he
    obtain ⟨hz, hm, ho⟩ := h5 e he'
    have hu' := hu e he'
    by_cases h1 : u e = 1
    · have : e ∈ S := by rw [hS]; exact ⟨he', h1⟩
      simp [Set.indicator_of_mem this, h1]
    · have : e ∉ S := by rw [hS]; intro h; exact h1 h.2
      rw [Set.indicator_of_notMem this]
      rcases hu'.1.eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · have := hm h0 (lt_of_le_of_ne hu'.2 h1)
        rw [this]; ring
  have hE' : setWeight (dualVector Fp Fm lam) S =
      ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (((B ∩ S).ncard : ℝ) - ((D ∩ S).ncard : ℝ)) := by
    rw [Dev.Eq6.sum_support]
    · have h1 : setWeight (dualVector Fp Fm lam) S =
          ∑ e ∈ hE.toFinset, (S.indicator (1 : α → ℝ)) e * dualVector Fp Fm lam e := by
        rw [Dev.Eq6.setWeight_eq_sum hE hSE]
        apply Finset.sum_congr rfl
        intro e _
        rw [Dev.Eq6.indicator_eq, mul_comm]
      rw [h1, ← Dev.Eq6.weak_sum hE Fp Fm hFpE hFmE _ lam]
      apply Finset.sum_congr rfl; intro B hB
      apply Finset.sum_congr rfl; intro D hD
      rw [Dev.Eq6.setWeight_indicator_ncard hE (hFpE B hB) hSE,
        Dev.Eq6.setWeight_indicator_ncard hE (hFmE D hD) hSE]
    · intro B hB D hD hn
      have : lam B D = 0 := le_antisymm (not_lt.1 hn) (hlam B hB D hD)
      rw [this]; ring
  exact ⟨by rw [hA, hB], by rw [hA, hC], hD, hE'⟩

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_proof_theorem_2_eq_6 := @MatroidEquitability.chk_proof_theorem_2_eq_6
