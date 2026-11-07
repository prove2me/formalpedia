-- Prove2me | solution 1 for HighOrderWalks.OneSided.proposition_4_1_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:54:21.388629+00:00
-- url     : https://prove2.me/submissions/2e9d7a82-0b84-47ba-ac05-9f6a01c565f6

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

theorem HighOrderWalks.OneSided.proposition_4_1_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose (l + 1) c : ℝ) * ip X m (l + 1) φ ψ =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l + 1 - c) (loc φ τ) (loc ψ τ) := by
  exact WalksLocalInner.local_inner hX.1 m c (l + 1) (by omega) φ ψ



namespace HOW54
def U {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (σ : Finset V) : Finset (Finset V) :=
  X.filter (fun ρ => ρ.card = σ.card + 1 ∧ σ ⊆ ρ)
end HOW54


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLocalInner

namespace WalksLocalAdjoint

variable {V : Type*} [DecidableEq V]

lemma link_up_sum {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (τ η : Finset V)
    (hη : η ∈ link X τ) (F : Finset V → ℝ) :
    (∑ σ ∈ U (link X τ) η, F (τ ∪ σ)) = ∑ ρ ∈ U X (τ ∪ η), F ρ := by
  obtain ⟨hηX, hdη, huη⟩ := Finset.mem_filter.mp hη
  have hcη := Finset.card_union_eq_card_add_card.mpr hdη
  apply Finset.sum_nbij' (fun σ => τ ∪ σ) (fun ρ => ρ \ τ)
  · intro σ hσ
    simp only [U, link, Finset.mem_filter] at hσ ⊢
    obtain ⟨⟨hσX, hdσ, huσ⟩, hσc, hησ⟩ := hσ
    refine ⟨huσ, ?_, Finset.union_subset_union (Finset.Subset.refl _) hησ⟩
    rw [Finset.card_union_eq_card_add_card.mpr hdσ, hcη, hσc]
    omega
  · intro ρ hρ
    simp only [U, link, Finset.mem_filter] at hρ ⊢
    obtain ⟨hρX, hρc, hsub⟩ := hρ
    have hτρ : τ ⊆ ρ := Finset.subset_union_left.trans hsub
    refine ⟨⟨hdc ρ hρX _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩, ?_, ?_⟩
    · rw [Finset.union_sdiff_of_subset hτρ]; exact hρX
    · have h := Finset.card_sdiff_add_card_eq_card hτρ
      omega
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_union_right _ hv),
        fun ht => Finset.disjoint_left.mp hdη ht hv⟩
  · intro σ hσ
    simp only [U, link, Finset.mem_filter] at hσ
    exact Finset.union_sdiff_cancel_left hσ.1.2.1
  · intro ρ hρ
    exact Finset.union_sdiff_of_subset (Finset.subset_union_left.trans (Finset.mem_filter.mp hρ).2.2)
  · intros; rfl

lemma local_dStar {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    (τ η : Finset V) (hη : η ∈ link X τ) (φ : Finset V → ℝ) :
    dStar (link X τ) (linkWeight m τ) (loc φ τ) η = dStar X m φ (τ ∪ η) := by
  have huη := (Finset.mem_filter.mp hη).2.2
  have h := link_up_sum hdc τ η hη (fun ρ => m ρ / m (τ ∪ η) * φ ρ)
  simpa only [U, and_comm, dStar, if_pos hη, if_pos huη, linkWeight, loc] using h

end WalksLocalAdjoint

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose l c : ℝ) * ip X m l (dStar X m φ) (dStar X m ψ) =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l - c)
        (dStar (link X τ) (linkWeight m τ) (loc φ τ))
        (dStar (link X τ) (linkWeight m τ) (loc ψ τ)) := by
  rw [WalksLocalInner.local_inner hX.1 m c l hcl]
  apply Finset.sum_congr rfl
  intro τ _
  unfold ip
  apply Finset.sum_congr rfl
  intro η hη
  rw [WalksLocalAdjoint.local_dStar hX.1 m τ η (Finset.mem_filter.mp hη).1,
    WalksLocalAdjoint.local_dStar hX.1 m τ η (Finset.mem_filter.mp hη).1]
  rfl


#print axioms solution
