-- Prove2me | solution 1 for MetricMSO.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:54:59.428013+00:00
-- url     : https://prove2.me/submissions/babe4d40-6dc8-475e-9d1a-0e0de87a6f89

import Mathlib
import Definitions.Def_MetricMSO_cbl

open MetricMSO

namespace Aux21

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact False.elim (hx rfl)
  · rfl

lemma cycle_length_le_card {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) : c.length ≤ Fintype.card V := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hlen : c.support.tail.length ≤ Fintype.card V := hnodup.length_le_card
  have hsup : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  omega

lemma shortCycleSpan_card_eq {V : Type} [Fintype V] (G : SimpleGraph V) :
    shortCycleSpan G (Fintype.card V) = cycleSpace G := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro f ⟨v, c, hc, _, rfl⟩
    exact ⟨v, c, hc, rfl⟩
  · apply Submodule.span_mono
    rintro f ⟨v, c, hc, rfl⟩
    exact ⟨v, c, hc, cycle_length_le_card hc, rfl⟩

lemma shortCycleSpan_cbl {V : Type} [Fintype V] (G : SimpleGraph V) :
    shortCycleSpan G (cbl G) = cycleSpace G := by
  unfold cbl
  exact Nat.sInf_mem (s := {L | shortCycleSpan G L = cycleSpace G})
    ⟨Fintype.card V, shortCycleSpan_card_eq G⟩

end Aux21

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) {k : ℕ} (B : Fin k → CycleOf G)
    (hB : IsMinCycleBasis B) :
    Finset.univ.sup (fun i => (B i).walk.length) = cbl G := by
  set L₀ := Finset.univ.sup (fun i => (B i).walk.length)
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro i₀ _
    by_contra! hgt
    let v : Fin k → (Sym2 V → ZMod 2) := fun i => cycleVec (B i).walk
    have hlin : LinearIndependent (ZMod 2) v := hB.1.1
    have hspan : Submodule.span (ZMod 2) (Set.range v) = cycleSpace G := hB.1.2
    let H : Submodule (ZMod 2) (Sym2 V → ZMod 2) :=
      Submodule.span (ZMod 2) (v '' {i : Fin k | i ≠ i₀})
    have hvi₀_not_H : v i₀ ∉ H := by
      intro hmem
      rw [Fintype.mem_span_image_iff_exists_fun] at hmem
      obtain ⟨c, hc⟩ := hmem
      let coeff : Fin k → ZMod 2 := fun i => if h : i = i₀ then -1 else c ⟨i, h⟩
      have hlin' := Fintype.linearIndependent_iff.mp hlin coeff
        (by
          have hsum : (∑ i : Fin k, coeff i • v i) =
              (-1 : ZMod 2) • v i₀ + ∑ i ∈ Finset.univ.erase i₀, coeff i • v i := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
            simp [coeff]
          have hc' : (∑ i : {i : Fin k | i ≠ i₀}, c i • v i) =
              ∑ i ∈ Finset.univ.erase i₀, coeff i • v i := by
            refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
            · intro x _; exact Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩
            · intro x₁ _ x₂ _ h; exact Subtype.ext h
            · intro j hj; exact ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, Finset.mem_univ _, rfl⟩
            · intro x _
              have hx : x.1 ≠ i₀ := x.2
              simp [coeff, hx]
          rw [hsum, ← hc', hc, neg_one_smul, neg_add_cancel])
      have h0 := hlin' i₀
      simp [coeff] at h0
    have hshort_not_le : ¬ shortCycleSpan G (cbl G) ≤ H := by
      rw [Aux21.shortCycleSpan_cbl G, ← hspan]
      intro hle
      exact hvi₀_not_H (hle (Submodule.subset_span ⟨i₀, rfl⟩))
    have hex : ∃ (vc : V) (c : G.Walk vc vc), c.IsCycle ∧ c.length ≤ cbl G ∧ cycleVec c ∉ H := by
      by_contra! hall
      apply hshort_not_le
      rw [shortCycleSpan, Submodule.span_le]
      rintro f ⟨vc, c, hc, hlen, rfl⟩
      exact hall vc c hc hlen
    obtain ⟨vc, c, hc_cyc, hc_len, hc_not_H⟩ := hex
    have hc_mem : cycleVec c ∈ Submodule.span (ZMod 2) (v '' (Set.univ : Set (Fin k))) := by
      rw [Set.image_univ, hspan]
      exact Submodule.subset_span ⟨vc, c, hc_cyc, rfl⟩
    rw [Fintype.mem_span_image_iff_exists_fun] at hc_mem
    obtain ⟨a', ha'⟩ := hc_mem
    let a : Fin k → ZMod 2 := fun j => a' ⟨j, trivial⟩
    have ha : (∑ j : Fin k, a j • v j) = cycleVec c := by
      rw [← ha']
      refine Finset.sum_bij (fun j _ => ⟨j, trivial⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro j₁ _ j₂ _ h; exact Subtype.mk.inj h
      · intro x _; exact ⟨x.1, Finset.mem_univ _, rfl⟩
      · intro _ _; rfl
    have hai₀_ne : a i₀ ≠ 0 := by
      intro hai₀
      apply hc_not_H
      rw [← ha]
      refine Submodule.sum_mem H fun j _ => ?_
      rcases eq_or_ne j i₀ with rfl | hj
      · simp [hai₀]
      · exact Submodule.smul_mem H (a j) (Submodule.subset_span ⟨j, hj, rfl⟩)
    have hai₀ : a i₀ = 1 := Aux21.zmod2_eq_one_of_ne_zero hai₀_ne
    let B' : Fin k → CycleOf G := fun j => if j = i₀ then ⟨vc, c, hc_cyc⟩ else B j
    have hB'_ne : ∀ j, j ≠ i₀ → B' j = B j := fun j hj => if_neg hj
    have hB'_eq : B' i₀ = ⟨vc, c, hc_cyc⟩ := if_pos rfl
    let w : Fin k → (Sym2 V → ZMod 2) := fun i => cycleVec (B' i).walk
    have hw_eq : ∀ j, j ≠ i₀ → w j = v j := by
      intro j hj; dsimp [w, v]; rw [hB'_ne j hj]
    have hwi₀ : w i₀ = cycleVec c := by
      dsimp [w]; rw [hB'_eq]
    have hc_decomp : cycleVec c = v i₀ + ∑ j ∈ Finset.univ.erase i₀, a j • v j := by
      rw [← ha, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hai₀, one_smul]
    have hB'_basis : IsCycleBasis B' := by
      refine ⟨Fintype.linearIndependent_iff.mpr ?_, ?_⟩
      · intro b hb
        have hb' : b i₀ • v i₀ + ∑ j ∈ Finset.univ.erase i₀, (b j + b i₀ * a j) • v j = 0 := by
          have h1 : (∑ j : Fin k, b j • w j) =
              b i₀ • w i₀ + ∑ j ∈ Finset.univ.erase i₀, b j • v j := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
            congr 1
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [hw_eq j (Finset.ne_of_mem_erase hj)]
          rw [h1, hwi₀, hc_decomp, smul_add, Finset.smul_sum, add_assoc, ← Finset.sum_add_distrib] at hb
          convert hb using 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [add_smul, mul_smul, add_comm]
        have hb'' : (∑ j : Fin k, (if j = i₀ then b i₀ else b j + b i₀ * a j) • v j) = 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
          simp only [↓reduceIte]
          convert hb' using 2
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [if_neg (Finset.ne_of_mem_erase hj)]
        have hall0 := Fintype.linearIndependent_iff.mp hlin _ hb''
        have hbi₀ : b i₀ = 0 := by simpa using hall0 i₀
        intro j
        rcases eq_or_ne j i₀ with rfl | hj
        · exact hbi₀
        · have hj0 := hall0 j
          simp [hj, hbi₀] at hj0
          exact hj0
      · apply le_antisymm
        · rw [Submodule.span_le]
          rintro f ⟨j, rfl⟩
          change w j ∈ (cycleSpace G : Set (Sym2 V → ZMod 2))
          rcases eq_or_ne j i₀ with rfl | hj
          · rw [hwi₀]
            exact Submodule.subset_span ⟨vc, c, hc_cyc, rfl⟩
          · rw [hw_eq j hj, ← hspan]
            exact Submodule.subset_span ⟨j, rfl⟩
        · rw [← hspan, Submodule.span_le]
          rintro f ⟨j, rfl⟩
          change v j ∈ (Submodule.span (ZMod 2) (Set.range w) : Set (Sym2 V → ZMod 2))
          rcases eq_or_ne j i₀ with rfl | hj
          · have hsum_mem : (∑ l ∈ Finset.univ.erase j, a l • v l) ∈
                Submodule.span (ZMod 2) (Set.range w) := by
              refine Submodule.sum_mem _ fun l hl => ?_
              rw [← hw_eq l (Finset.ne_of_mem_erase hl)]
              exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
            have hvi₀_eq : v j = w j - ∑ l ∈ Finset.univ.erase j, a l • v l := by
              rw [hwi₀, hc_decomp, add_sub_cancel_right]
            rw [hvi₀_eq]
            exact Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩) hsum_mem
          · rw [← hw_eq j hj]
            exact Submodule.subset_span ⟨j, rfl⟩
    have hmin := hB.2 k B' hB'_basis
    have hsum_B : ∑ j : Fin k, (B j).walk.length =
        (B i₀).walk.length + ∑ j ∈ Finset.univ.erase i₀, (B j).walk.length :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    have hsum_B' : ∑ j : Fin k, (B' j).walk.length =
        c.length + ∑ j ∈ Finset.univ.erase i₀, (B j).walk.length := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have hhead : (B' i₀).walk.length = c.length := by rw [hB'_eq]
      rw [hhead]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hB'_ne j (Finset.ne_of_mem_erase hj)]
    omega
  · unfold cbl
    apply Nat.sInf_le
    change shortCycleSpan G L₀ = cycleSpace G
    apply le_antisymm
    · apply Submodule.span_mono
      rintro f ⟨v, c, hc, _, rfl⟩
      exact ⟨v, c, hc, rfl⟩
    · rw [← hB.1.2, Submodule.span_le]
      rintro f ⟨i, rfl⟩
      exact Submodule.subset_span
        ⟨(B i).base, (B i).walk, (B i).isCycle,
          Finset.le_sup (f := fun j => (B j).walk.length) (Finset.mem_univ i), rfl⟩
