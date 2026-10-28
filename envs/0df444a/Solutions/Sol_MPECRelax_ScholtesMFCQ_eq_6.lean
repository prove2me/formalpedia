-- Prove2me | solution 1 for MPECRelax.ScholtesMFCQ.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:20:20.303241+00:00
-- url     : https://prove2.me/submissions/f690e971-8867-4718-ac09-5f8c3220e991

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

open MPECRelax.ScholtesMFCQ in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : MPECRelax.ScholtesConv.E n)
    (hfeas : P.Feasible xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x →
      P.Ig x ⊆ P.Ig xs ∧ P.IG x ⊆ P.I00 xs ∪ P.I0p xs ∧ P.IH x ⊆ P.I00 xs ∪ P.Ip0 xs ∧
        P.IGH x t ∩ P.IG x = ∅ ∧ P.IGH x t ∩ P.IH x = ∅ := by
  obtain ⟨_, hgC, _, hGC, hHC⟩ := hP
  have hg : ∀ᶠ x in 𝓝 xs, ∀ i, P.g i xs < 0 → P.g i x < 0 := by
    rw [Filter.eventually_all]; intro i
    by_cases h : P.g i xs < 0
    · exact (((hgC i).continuous.continuousAt).eventually_lt continuousAt_const h).mono
        fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h' => absurd h' h
  have hG : ∀ᶠ x in 𝓝 xs, ∀ i, 0 < P.G i xs → 0 < P.G i x := by
    rw [Filter.eventually_all]; intro i
    by_cases h : 0 < P.G i xs
    · exact ((continuousAt_const).eventually_lt ((hGC i).continuous.continuousAt) h).mono
        fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h' => absurd h' h
  have hH : ∀ᶠ x in 𝓝 xs, ∀ i, 0 < P.H i xs → 0 < P.H i x := by
    rw [Filter.eventually_all]; intro i
    by_cases h : 0 < P.H i xs
    · exact ((continuousAt_const).eventually_lt ((hHC i).continuous.continuousAt) h).mono
        fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h' => absurd h' h
  refine ⟨_, hg.and (hG.and hH), ?_⟩
  intro t ht x hx _
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [MPEC.Ig, Set.mem_setOf_eq] at hi ⊢
    by_contra hne
    have := lt_of_le_of_ne (hfeas.1 i) hne
    linarith [hx1 i this]
  · intro i hi
    simp only [MPEC.IG, MPEC.I00, MPEC.I0p, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    have hG0 : P.G i xs = 0 := by
      by_contra hne
      have := lt_of_le_of_ne (hfeas.2.2 i).1 (Ne.symm hne)
      linarith [hx2 i this]
    rcases (hfeas.2.2 i).2.1.eq_or_lt with h | h
    · left; exact ⟨hG0, h.symm⟩
    · right; exact ⟨hG0, h⟩
  · intro i hi
    simp only [MPEC.IH, MPEC.I00, MPEC.Ip0, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    have hH0 : P.H i xs = 0 := by
      by_contra hne
      have := lt_of_le_of_ne (hfeas.2.2 i).2.1 (Ne.symm hne)
      linarith [hx3 i this]
    rcases (hfeas.2.2 i).1.eq_or_lt with h | h
    · left; exact ⟨h.symm, hH0⟩
    · right; exact ⟨h, hH0⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro i ⟨h1, h2⟩
    simp only [MPEC.IGH, MPEC.IG, Set.mem_setOf_eq] at h1 h2
    rw [h2, mul_zero] at h1
    linarith
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro i ⟨h1, h2⟩
    simp only [MPEC.IGH, MPEC.IH, Set.mem_setOf_eq] at h1 h2
    rw [h2, zero_mul] at h1
    linarith
