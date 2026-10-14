-- Prove2me | solution 1 for KangKurtz.SecondScale.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:02:10.689959+00:00
-- url     : https://prove2.me/submissions/d871c560-b6b7-48e2-9847-efc092f19526

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting

namespace RRAux_KangKurtz_SecondScale_lemma_4_4

open KangKurtz.SecondScale

theorem mem_sp {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) {k : Fin r} {i : Fin s}
    (h : ν k i ≠ ν' k i) : k ∈ GammaSpPlus ν ν' i ∪ GammaSpMinus ν ν' i := by
  simp only [GammaSpPlus, GammaSpMinus, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

theorem gs_le {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    {k : Fin r} {i : Fin s} (h : ν k i ≠ ν' k i) :
    gammaSp ν ν' α β i ≤ ((α i - KangKurtz.SCC.rho ν α β k : ℝ) : EReal) := by
  have hk := mem_sp ν ν' h
  unfold gammaSp
  rw [dif_pos ⟨k, hk⟩]
  apply EReal.coe_le_coe_iff.mpr
  have := Finset.le_sup' (KangKurtz.SCC.rho ν α β) hk
  linarith

theorem zeta_ne {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) {k : Fin r} {i : Fin s}
    (h : KangKurtz.SCC.zeta ν ν' k i ≠ 0) : ν k i ≠ ν' k i := by
  intro he
  apply h
  unfold KangKurtz.SCC.zeta
  rw [he]
  ring

theorem r1_real {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    (hζ : ∃ k i, ν' k i ≠ ν k i) : ∃ x : ℝ, r1 ν ν' α β = (x : EReal) := by
  obtain ⟨k, i, hki⟩ := hζ
  have : Nonempty (Fin s) := ⟨i⟩
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := fun i => gammaSp ν ν' α β i)
  have hlt : r1 ν ν' α β < ⊤ := by
    unfold r1
    exact lt_of_le_of_lt (iInf_le _ i)
      (lt_of_le_of_lt (gs_le ν ν' α β (Ne.symm hki)) (EReal.coe_lt_top _))
  unfold r1 at hlt ⊢
  rw [← hi0] at hlt ⊢
  unfold gammaSp at hlt ⊢
  by_cases hne : (GammaSpPlus ν ν' i0 ∪ GammaSpMinus ν ν' i0).Nonempty
  · rw [dif_pos hne]
    exact ⟨_, rfl⟩
  · rw [dif_neg hne] at hlt
    exact absurd hlt (lt_irrefl _)

end RRAux_KangKurtz_SecondScale_lemma_4_4

open KangKurtz.SecondScale in
theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (hζ : ∃ k i, ν' k i ≠ ν k i) :
    r1 ν ν' α β < r2 ν ν' α β := by
  classical
  obtain ⟨x, hx⟩ := RRAux_KangKurtz_SecondScale_lemma_4_4.r1_real ν ν' α β hζ
  have hxle : ∀ i, (x : EReal) ≤ gammaSp ν ν' α β i := by
    intro i; rw [← hx]; exact iInf_le _ i
  have hxle' : ∀ i k, ν k i ≠ ν' k i → x ≤ α i - KangKurtz.SCC.rho ν α β k := by
    intro i k h
    exact EReal.coe_le_coe_iff.mp
      (le_trans (hxle i) (RRAux_KangKurtz_SecondScale_lemma_4_4.gs_le ν ν' α β h))
  let f : Fin s × Fin r → EReal := fun p =>
    if x < α p.1 - KangKurtz.SCC.rho ν α β p.2 then
      ((α p.1 - KangKurtz.SCC.rho ν α β p.2 : ℝ) : EReal) else ⊤
  have hb : (x : EReal) < ⨅ p, f p := by
    obtain ⟨k, i, _⟩ := hζ
    have : Nonempty (Fin s × Fin r) := ⟨(i, k)⟩
    obtain ⟨p, hp⟩ := exists_eq_ciInf_of_finite (f := f)
    rw [← hp]
    simp only [f]
    split_ifs with h
    · exact EReal.coe_lt_coe_iff.mpr h
    · exact EReal.coe_lt_top x
  rw [hx]
  refine lt_of_lt_of_le hb ?_
  unfold r2
  refine le_iInf₂ (fun θ hθ => ?_)
  obtain ⟨hθnn, hθK⟩ := hθ
  unfold KangKurtz.SCC.gammaTheta
  simp only []
  by_cases hne : (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).Nonempty
  swap
  · rw [dif_neg hne]; exact le_top
  rw [dif_pos hne]
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' hne (KangKurtz.SCC.rho ν α β)
  rw [heq]
  have hdot : KangKurtz.SCC.dot ν ν' θ k ≠ 0 := by
    simp only [KangKurtz.SCC.GammaPlus, KangKurtz.SCC.GammaMinus, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hk with h | h
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hsupp : (Finset.univ.filter (fun i => 0 < θ i)).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    apply hdot
    unfold KangKurtz.SCC.dot
    apply Finset.sum_eq_zero
    intro i _
    have : θ i = 0 := le_antisymm (not_lt.mp (hc (Finset.mem_univ i))) (hθnn i)
    simp [this]
  obtain ⟨i0, hi0, hi0eq⟩ := Finset.exists_mem_eq_sup' hsupp α
  have halpha : KangKurtz.SCC.alphaTheta α θ = α i0 := by
    unfold KangKurtz.SCC.alphaTheta
    simp only []
    rw [dif_pos hsupp, hi0eq]
  rw [halpha]
  have hstrict : x < α i0 - KangKurtz.SCC.rho ν α β k := by
    by_contra hle
    push Not at hle
    -- every changed species in the support is in S1
    have hS : ∀ i, 0 < θ i → KangKurtz.SCC.zeta ν ν' k i ≠ 0 →
        k ∈ GammaR1 ν ν' α β i := by
      intro i hi hz
      have hch := RRAux_KangKurtz_SecondScale_lemma_4_4.zeta_ne ν ν' hz
      have h1 := hxle' i k hch
      have h2 : α i ≤ α i0 := by
        rw [← hi0eq]
        exact Finset.le_sup' α (by simpa using hi)
      have h3 : x + KangKurtz.SCC.rho ν α β k = α i := by linarith
      simp only [GammaR1, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hx, ← EReal.coe_add, h3]
    obtain ⟨i1, _, hi1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdot
    have hθi1 : θ i1 ≠ 0 := left_ne_zero_of_mul hi1
    have hz1 : KangKurtz.SCC.zeta ν ν' k i1 ≠ 0 := right_ne_zero_of_mul hi1
    have hK := hθK k ⟨i1, hS i1 (lt_of_le_of_ne (hθnn i1) (Ne.symm hθi1)) hz1⟩
    apply hdot
    rw [← hK]
    unfold KangKurtz.SCC.dot
    apply Finset.sum_congr rfl
    intro i _
    unfold Pi1
    split_ifs with hiS
    · rfl
    · rw [mul_zero]
      by_contra hc
      have hθi : θ i ≠ 0 := left_ne_zero_of_mul hc
      have hzi : KangKurtz.SCC.zeta ν ν' k i ≠ 0 := right_ne_zero_of_mul hc
      apply hiS
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, hS i (lt_of_le_of_ne (hθnn i) (Ne.symm hθi)) hzi⟩
  refine le_trans (iInf_le f (i0, k)) ?_
  simp only [f, if_pos hstrict]
  exact le_refl _

#print axioms solution
