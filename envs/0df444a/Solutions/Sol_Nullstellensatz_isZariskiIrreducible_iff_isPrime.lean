-- Prove2me | solution 1 for Nullstellensatz.isZariskiIrreducible_iff_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:41:52.230863+00:00
-- url     : https://prove2.me/submissions/69907e86-67db-417b-a3f5-e2c42ab3aa69

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem aux_zirr_mem_vanishingIdeal {K : Type*} [Field K] {n : ℕ}
    (U : Set (Fin n → K)) (p : MvPolynomial (Fin n) K) :
    p ∈ vanishingIdeal U ↔ ∀ a ∈ U, eval a p = 0 := Iff.rfl

theorem aux_zirr_mem_zeroSet_span {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (b : Fin n → K) :
    b ∈ zeroSet (Ideal.span {f}) ↔ eval b f = 0 := by
  constructor
  · intro h
    exact h f (Ideal.subset_span rfl)
  · intro h p hp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h]

end Nullstellensatz

open Nullstellensatz

theorem solution {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (W : Set (Fin n → K)) (hW : IsAlgebraicSet W) :
    IsZariskiIrreducible W ↔ (vanishingIdeal W).IsPrime := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin n) K) ∈ vanishingIdeal W := by
        rw [htop]; exact Submodule.mem_top
      have := (aux_zirr_mem_vanishingIdeal W 1).mp h1 a ha
      simp at this
    · intro f g hfg
      rw [aux_zirr_mem_vanishingIdeal] at hfg
      have h1 : IsAlgebraicSet (zeroSet (Ideal.span {f}) : Set (Fin n → K)) := ⟨_, rfl⟩
      have h2 : IsAlgebraicSet (zeroSet (Ideal.span {g}) : Set (Fin n → K)) := ⟨_, rfl⟩
      have hsub : W ⊆ zeroSet (Ideal.span {f}) ∪ zeroSet (Ideal.span {g}) := by
        intro b hb
        have hb' : eval b (f * g) = 0 := hfg b hb
        rw [map_mul, mul_eq_zero] at hb'
        rcases hb' with h | h
        · left
          exact (aux_zirr_mem_zeroSet_span f b).mpr h
        · right
          exact (aux_zirr_mem_zeroSet_span g b).mpr h
      rcases h _ _ h1 h2 hsub with hs | hs
      · left
        rw [aux_zirr_mem_vanishingIdeal]
        intro b hb
        exact (aux_zirr_mem_zeroSet_span f b).mp (hs hb)
      · right
        rw [aux_zirr_mem_vanishingIdeal]
        intro b hb
        exact (aux_zirr_mem_zeroSet_span g b).mp (hs hb)
  · intro hP
    refine ⟨?_, ?_⟩
    · by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, aux_zirr_mem_vanishingIdeal]
      intro a ha
      rw [hne] at ha
      exact ha.elim
    · rintro W₁ W₂ ⟨J₁, rfl⟩ ⟨J₂, rfl⟩ hsub
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [Set.not_subset] at h1 h2
      obtain ⟨a, ha, ha1⟩ := h1
      obtain ⟨b, hb, hb2⟩ := h2
      simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at ha1 hb2
      obtain ⟨f, hf, hfa⟩ := ha1
      obtain ⟨g, hg, hgb⟩ := hb2
      have hfg : f * g ∈ vanishingIdeal W := by
        rw [aux_zirr_mem_vanishingIdeal]
        intro c hc
        rcases hsub hc with hc1 | hc2
        · rw [map_mul, hc1 f hf, zero_mul]
        · rw [map_mul, hc2 g hg, mul_zero]
      rcases hP.mem_or_mem hfg with hf' | hg'
      · exact hfa ((aux_zirr_mem_vanishingIdeal W f).mp hf' a ha)
      · exact hgb ((aux_zirr_mem_vanishingIdeal W g).mp hg' b hb)
