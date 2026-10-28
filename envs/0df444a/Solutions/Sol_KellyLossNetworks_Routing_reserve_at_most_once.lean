-- Prove2me | solution 1 for KellyLossNetworks.Routing.reserve_at_most_once
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:59:55.758236+00:00
-- url     : https://prove2.me/submissions/e1ea0762-d667-46c5-9ab0-942ec55d429f

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace Aux_KLNR
open KellyLossNetworks.Routing

lemma pos_imp {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (e : Edge K) (k : Fin K)
    (h : 0 < reserve C D x e k) : C < x e ∧ ∀ g, OnDetour e k g → x g < C := by
  classical
  unfold reserve at h
  split_ifs at h with hk
  · exact absurd h (lt_irrefl 0)
  · set N := max (x e - C) 0 * (∏ g ∈ Finset.univ.filter (OnDetour e k), max (C - x g) 0)
      with hN
    have hP0 : 0 ≤ ∏ g ∈ Finset.univ.filter (OnDetour e k), max (C - x g) 0 :=
      Finset.prod_nonneg fun g _ => le_max_right _ _
    have hN0 : 0 ≤ N := mul_nonneg (le_max_right _ _) hP0
    have hNne : N ≠ 0 := by
      intro h0
      rw [h0, zero_div] at h
      exact lt_irrefl 0 h
    have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNne)
    have h1 : max (x e - C) 0 ≠ 0 := fun h0 => hNne (by rw [hN, h0, zero_mul])
    have h2 : (∏ g ∈ Finset.univ.filter (OnDetour e k), max (C - x g) 0) ≠ 0 :=
      fun h0 => hNne (by rw [hN, h0, mul_zero])
    refine ⟨?_, fun g hg => ?_⟩
    · by_contra hc
      push Not at hc
      exact h1 (max_eq_right (by linarith))
    · have hmem : g ∈ Finset.univ.filter (OnDetour e k) := by simp [hg]
      have := Finset.prod_ne_zero_iff.mp h2 g hmem
      by_contra hc
      push Not at hc
      exact this (max_eq_right (by linarith))

end Aux_KLNR

open KellyLossNetworks.Routing in
theorem solution {K : ℕ} (C D : ℝ) (hD : 0 < D) (x : Edge K → ℝ)
    (a b c : Fin K) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (e₁ e₂ e₃ : Edge K) (h₁ : e₁.1 = s(a, b)) (h₂ : e₂.1 = s(b, c)) (h₃ : e₃.1 = s(c, a)) :
    ¬ (0 < reserve C D x e₁ c ∧ 0 < reserve C D x e₂ a) ∧
    ¬ (0 < reserve C D x e₂ a ∧ 0 < reserve C D x e₃ b) ∧
    ¬ (0 < reserve C D x e₃ b ∧ 0 < reserve C D x e₁ c) ∧
    ∀ (e : Edge K) (k : Fin K), 0 < reserve C D x e k →
      C < x e ∧ ∀ g, OnDetour e k g → x g < C := by
  have d12 : OnDetour e₁ c e₂ := by
    refine ⟨?_, b, ?_, ?_⟩
    · rw [h₁, Sym2.mem_iff]; rintro (h | h)
      · exact hca h
      · exact hbc h.symm
    · rw [h₁]; exact Sym2.mem_mk_right a b
    · rw [h₂]
  have d23 : OnDetour e₂ a e₃ := by
    refine ⟨?_, c, ?_, ?_⟩
    · rw [h₂, Sym2.mem_iff]; rintro (h | h)
      · exact hab h
      · exact hca h.symm
    · rw [h₂]; exact Sym2.mem_mk_right b c
    · rw [h₃]
  have d31 : OnDetour e₃ b e₁ := by
    refine ⟨?_, a, ?_, ?_⟩
    · rw [h₃, Sym2.mem_iff]; rintro (h | h)
      · exact hbc h
      · exact hab h.symm
    · rw [h₃]; exact Sym2.mem_mk_right c a
    · rw [h₁]
  refine ⟨?_, ?_, ?_, fun e k h => Aux_KLNR.pos_imp C D x e k h⟩
  · rintro ⟨r1, r2⟩
    have := (Aux_KLNR.pos_imp C D x _ _ r1).2 _ d12
    have := (Aux_KLNR.pos_imp C D x _ _ r2).1
    linarith
  · rintro ⟨r1, r2⟩
    have := (Aux_KLNR.pos_imp C D x _ _ r1).2 _ d23
    have := (Aux_KLNR.pos_imp C D x _ _ r2).1
    linarith
  · rintro ⟨r1, r2⟩
    have := (Aux_KLNR.pos_imp C D x _ _ r1).2 _ d31
    have := (Aux_KLNR.pos_imp C D x _ _ r2).1
    linarith
