-- Prove2me | solution 1 for HighOrderWalks.TwoSided.proposition_4_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:54:22.142062+00:00
-- url     : https://prove2.me/submissions/575456e4-6d9b-433f-b455-0a501e7e79aa

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided Finset

namespace WalksLocalInner

variable {V : Type*} [DecidableEq V]

lemma link_sum {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (τ : Finset V) (r : ℕ) (F : Finset V → ℝ) :
    ∑ η ∈ cells (link X τ) r, F (τ ∪ η) =
      ∑ σ ∈ X.filter (fun σ => σ.card = τ.card + r ∧ τ ⊆ σ), F σ := by
  apply Finset.sum_nbij' (fun η => τ ∪ η) (fun σ => σ \ τ)
  · intro η hη
    simp only [cells, link, mem_filter] at hη ⊢
    obtain ⟨⟨_, hd, hu⟩, hr⟩ := hη
    exact ⟨hu, by rw [card_union_eq_card_add_card.mpr hd, hr], subset_union_left⟩
  · intro σ hσ
    simp only [cells, link, mem_filter] at hσ ⊢
    obtain ⟨hσX, hc, hsub⟩ := hσ
    refine ⟨⟨hdc σ hσX _ sdiff_subset, disjoint_sdiff, ?_⟩, ?_⟩
    · rw [union_sdiff_of_subset hsub]; exact hσX
    · have h := card_sdiff_add_card_eq_card hsub; omega
  · intro η hη
    simp only [cells, link, mem_filter] at hη
    exact union_sdiff_cancel_left hη.1.2.1
  · intro σ hσ
    exact union_sdiff_of_subset (mem_filter.mp hσ).2.2
  · intros; rfl

lemma localization_count {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (c b : ℕ) (hcb : c ≤ b)
    (F : Finset V → ℝ) :
    (∑ τ ∈ cells X c, ∑ η ∈ cells (link X τ) (b - c), F (τ ∪ η)) =
      (Nat.choose b c : ℝ) * ∑ σ ∈ cells X b, F σ := by
  have hinner (τ : Finset V) (hτ : τ ∈ cells X c) :
      (∑ η ∈ cells (link X τ) (b - c), F (τ ∪ η)) =
        ∑ σ ∈ (cells X b).filter (fun σ => τ ⊆ σ), F σ := by
    rw [link_sum hdc]
    apply Finset.sum_congr
    · ext σ
      have hτc := (Finset.mem_filter.mp hτ).2
      simp [cells, hτc, Nat.add_sub_of_le hcb, and_assoc]
    · intros; rfl
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_comm' (t' := cells X b) (s' := fun σ => σ.powersetCard c)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.sum_const, Finset.card_powersetCard, (Finset.mem_filter.mp hσ).2,
      nsmul_eq_mul]
  · intro τ σ
    simp only [cells, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hτX, hτc⟩, ⟨hσX, hσb⟩, hsub⟩
      exact ⟨⟨hsub, hτc⟩, hσX, hσb⟩
    · rintro ⟨⟨hsub, hτc⟩, hσX, hσb⟩
      exact ⟨⟨hdc σ hσX τ hsub, hτc⟩, ⟨hσX, hσb⟩, hsub⟩

lemma local_inner {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    (c b : ℕ) (hcb : c ≤ b) (φ ψ : Finset V → ℝ) :
    (Nat.choose b c : ℝ) * ip X m b φ ψ =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (b - c) (loc φ τ) (loc ψ τ) := by
  exact (localization_count hdc c b hcb (fun σ => m σ * φ σ * ψ σ)).symm

end WalksLocalInner

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose (l + 1) c : ℝ) * ip X m (l + 1) φ ψ =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l + 1 - c) (loc φ τ) (loc ψ τ) := by
  exact WalksLocalInner.local_inner hX.1 m c (l + 1) (by omega) φ ψ

#print axioms solution
