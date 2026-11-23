-- Prove2me | solution 1 for ImplicitParityWL.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:25:23.91213+00:00
-- url     : https://prove2.me/submissions/3da2a65e-d309-4ba2-8494-1d99270a356b

import Mathlib
import Definitions.Def_ImplicitParityWL_Address

open ImplicitParityWL

namespace Aux_lemma_4_6

lemma two_diff_blocks {k ℓ : ℕ} {a a' : Address k ℓ} (hne : a ≠ a') :
    ∃ i₁ i₂ : Fin k, i₁ ≠ i₂ ∧ a.1 i₁ ≠ a'.1 i₁ ∧ a.1 i₂ ≠ a'.1 i₂ := by
  classical
  have hfn : a.1 ≠ a'.1 := Subtype.coe_ne_coe.mpr hne
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hfn
  by_contra hno
  push_neg at hno
  have heq_rest : ∀ i ∈ Finset.univ.erase i₁, a.1 i = a'.1 i := by
    intro i hi
    exact hno i₁ i (Finset.mem_erase.mp hi).1.symm hi₁
  have hsum_a : a.1 i₁ + ∑ i ∈ Finset.univ.erase i₁, a.1 i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
    exact a.2
  have hsum_a' : a'.1 i₁ + ∑ i ∈ Finset.univ.erase i₁, a'.1 i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
    exact a'.2
  rw [Finset.sum_congr rfl heq_rest] at hsum_a
  exact hi₁ (add_right_cancel (hsum_a.trans hsum_a'.symm))

lemma address_supp_card {k ℓ : ℕ} (a : Address k ℓ) : a.supp.card = k := by
  unfold Address.supp
  rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1), Finset.card_fin]

lemma mem_address_supp {k ℓ : ℕ} (a : Address k ℓ) (c : Coord k ℓ) :
    c ∈ a.supp ↔ c.2 = a.1 c.1 := by
  unfold Address.supp
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rfl
  · intro h
    exact ⟨c.1, Prod.ext rfl h.symm⟩

end Aux_lemma_4_6

theorem solution (k ℓ : ℕ) (_hk : 3 ≤ k) (_hℓ : 1 ≤ ℓ) :
    (∀ a a' : Address k ℓ, a ≠ a' → 4 ≤ hammingDist a.word a'.word) ∧
    (∀ I : Finset (Coord k ℓ), I.card ≤ k + 1 → ∀ a a' : Address k ℓ,
      a.supp ⊆ I → a'.supp ⊆ I → a = a') := by
  classical
  constructor
  · intro a a' hne
    obtain ⟨i₁, i₂, hi12, hd₁, hd₂⟩ := Aux_lemma_4_6.two_diff_blocks hne
    let c₁ : Coord k ℓ := (i₁, a.1 i₁)
    let c₂ : Coord k ℓ := (i₁, a'.1 i₁)
    let c₃ : Coord k ℓ := (i₂, a.1 i₂)
    let c₄ : Coord k ℓ := (i₂, a'.1 i₂)
    let S : Finset (Coord k ℓ) := {c₁, c₂, c₃, c₄}
    have hc12 : c₁ ≠ c₂ := fun h => hd₁ (Prod.mk.inj h).2
    have hc13 : c₁ ≠ c₃ := fun h => hi12 (Prod.mk.inj h).1
    have hc14 : c₁ ≠ c₄ := fun h => hi12 (Prod.mk.inj h).1
    have hc23 : c₂ ≠ c₃ := fun h => hi12 (Prod.mk.inj h).1
    have hc24 : c₂ ≠ c₄ := fun h => hi12 (Prod.mk.inj h).1
    have hc34 : c₃ ≠ c₄ := fun h => hd₂ (Prod.mk.inj h).2
    have hScard : S.card = 4 := by
      simp [S, c₁, c₂, c₃, c₄, hc12, hc13, hc14, hc23, hc24, hc34]
    have hsub : S ⊆ Finset.univ.filter (fun c => a.word c ≠ a'.word c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · simp [Address.word, c₁, hd₁]
      · simp [Address.word, c₂, Ne.symm hd₁]
      · simp [Address.word, c₃, hd₂]
      · simp [Address.word, c₄, Ne.symm hd₂]
    calc 4 = S.card := hScard.symm
      _ ≤ (Finset.univ.filter (fun c => a.word c ≠ a'.word c)).card := Finset.card_le_card hsub
      _ = hammingDist a.word a'.word := rfl
  · intro I hI a a' ha ha'
    by_contra hne
    obtain ⟨i₁, i₂, hi12, hd₁, hd₂⟩ := Aux_lemma_4_6.two_diff_blocks hne
    let c₂ : Coord k ℓ := (i₁, a'.1 i₁)
    let c₄ : Coord k ℓ := (i₂, a'.1 i₂)
    have hc₂_mem : c₂ ∈ I := ha' ((Aux_lemma_4_6.mem_address_supp a' c₂).mpr rfl)
    have hc₄_mem : c₄ ∈ I := ha' ((Aux_lemma_4_6.mem_address_supp a' c₄).mpr rfl)
    have hc₂_not : c₂ ∉ a.supp := by
      rw [Aux_lemma_4_6.mem_address_supp]
      exact Ne.symm hd₁
    have hc₄_not : c₄ ∉ a.supp := by
      rw [Aux_lemma_4_6.mem_address_supp]
      exact Ne.symm hd₂
    have hc24 : c₂ ≠ c₄ := fun h => hi12 (Prod.mk.inj h).1
    have hsub : insert c₂ (insert c₄ a.supp) ⊆ I := by
      intro c hc
      simp only [Finset.mem_insert] at hc
      rcases hc with rfl | rfl | hc
      · exact hc₂_mem
      · exact hc₄_mem
      · exact ha hc
    have hcard_le := Finset.card_le_card hsub
    have hc₂_not' : c₂ ∉ insert c₄ a.supp := by
      simp [hc24, hc₂_not]
    rw [Finset.card_insert_of_notMem hc₂_not', Finset.card_insert_of_notMem hc₄_not,
      Aux_lemma_4_6.address_supp_card] at hcard_le
    omega
