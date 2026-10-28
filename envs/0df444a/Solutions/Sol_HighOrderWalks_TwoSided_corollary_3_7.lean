-- Prove2me | solution 1 for HighOrderWalks.TwoSided.corollary_3_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:12:24.400901+00:00
-- url     : https://prove2.me/submissions/19f777c3-8000-449d-830a-583c9d42ffe2

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

namespace Aux_HOW_37

lemma sum_single {α : Type*} (S : Finset α) (a : α) (P : Prop) [Decidable P] (F : α → ℝ)
    (h1 : ∀ x ∈ S, x = a) (h2 : a ∈ S ↔ P) : ∑ x ∈ S, F x = if P then F a else 0 := by
  split_ifs with hP
  · rw [Finset.sum_eq_single_of_mem a (h2.mpr hP)]
    intro b hb hba; exact absurd (h1 b hb) hba
  · rw [Finset.sum_eq_zero]
    intro x hx
    have := h1 x hx
    subst this
    exact absurd (h2.mp hx) hP

variable {V : Type*} [DecidableEq V]

lemma union_eq (τ τ' σ : Finset V) (h1 : τ ⊆ σ) (h2 : τ' ⊆ σ) (hc1 : σ.card = τ.card + 1)
    (hc2 : τ'.card + 1 = σ.card) (hne : τ' ≠ τ) : σ = τ ∪ τ' := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.union_subset h1 h2)
  have : ¬ τ' ⊆ τ := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨x, hx1, hx2⟩ := Finset.not_subset.mp this
  have h3 : insert x τ ⊆ τ ∪ τ' :=
    Finset.insert_subset (Finset.mem_union_right _ hx1) Finset.subset_union_left
  have := Finset.card_le_card h3
  rw [Finset.card_insert_of_notMem hx2] at this
  omega

lemma inter_eq (τ τ' η : Finset V) (h1 : η ⊆ τ) (h2 : η ⊆ τ') (hc1 : η.card + 1 = τ.card)
    (hc2 : τ'.card = η.card + 1) (hne : τ' ≠ τ) : η = τ ∩ τ' := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_inter h1 h2)
  have : ¬ τ ⊆ τ' := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
  obtain ⟨x, hx1, hx2⟩ := Finset.not_subset.mp this
  have h3 : τ ∩ τ' ⊆ τ.erase x := fun y hy =>
    Finset.mem_erase.mpr ⟨fun h => hx2 (h ▸ (Finset.mem_inter.mp hy).2), (Finset.mem_inter.mp hy).1⟩
  have := Finset.card_le_card h3
  rw [Finset.card_erase_of_mem hx1] at this
  omega

end Aux_HOW_37

open HighOrderWalks.OneSided Aux_HOW_37 in
theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) :
    (∀ τ ∈ HighOrderWalks.OneSided.cells X (k + 1), HighOrderWalks.OneSided.dStar X m (HighOrderWalks.OneSided.dS X φ) τ = ((k : ℝ) + 2) * HighOrderWalks.OneSided.upperWalk X m φ τ) ∧
      (∀ τ ∈ HighOrderWalks.OneSided.cells X (k + 1), HighOrderWalks.OneSided.dS X (HighOrderWalks.OneSided.dStar X m φ) τ = ((k : ℝ) + 1) * HighOrderWalks.OneSided.lowerWalk X m φ τ) := by
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · obtain ⟨hτX, hτc⟩ := Finset.mem_filter.mp hτ
    have hmτ : m τ ≠ 0 := (hm.1 τ hτX).ne'
    have hcard : ((τ.card : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by rw [hτc]; push_cast; ring
    unfold dStar
    rw [if_pos hτX]
    have hds : ∀ σ ∈ X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1),
        m σ / m τ * dS X φ σ =
          ∑ τ' ∈ X.filter (fun τ' => τ' ⊆ σ ∧ τ'.card + 1 = σ.card), m σ / m τ * φ τ' := by
      intro σ hσ
      unfold dS
      rw [if_pos (Finset.mem_filter.mp hσ).1, Finset.mul_sum]
    rw [Finset.sum_congr rfl hds]
    rw [Finset.sum_comm' (t' := X) (s' := fun τ' => X.filter (fun σ =>
      (τ ⊆ σ ∧ σ.card = τ.card + 1) ∧ (τ' ⊆ σ ∧ τ'.card + 1 = σ.card)))
      (by intro x y; simp only [Finset.mem_filter]; tauto)]
    have hg : ∀ τ' ∈ X, ∑ σ ∈ X.filter (fun σ =>
        (τ ⊆ σ ∧ σ.card = τ.card + 1) ∧ (τ' ⊆ σ ∧ τ'.card + 1 = σ.card)), m σ / m τ * φ τ' =
        (if τ = τ' then φ τ else 0) +
          (if (τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∪ τ' ∈ X ∧ (τ ∪ τ').card = τ.card + 1) then
            m (τ ∪ τ') / m τ * φ τ' else 0) := by
      intro τ' hτ'X
      by_cases h : τ' = τ
      · subst h
        rw [if_pos rfl, if_neg (by tauto), add_zero, ← Finset.sum_mul, ← Finset.sum_div]
        have hw := hm.2 τ' hτ'X (by omega)
        have hf : X.filter (fun σ => (τ' ⊆ σ ∧ σ.card = τ'.card + 1) ∧
            (τ' ⊆ σ ∧ τ'.card + 1 = σ.card)) =
            X.filter (fun σ => σ.card = τ'.card + 1 ∧ τ' ⊆ σ) :=
          Finset.filter_congr (fun σ _ => ⟨fun ⟨⟨a, b⟩, _, _⟩ => ⟨b, a⟩,
            fun ⟨b, a⟩ => ⟨⟨a, b⟩, a, b.symm⟩⟩)
        rw [hf, ← hw, div_self hmτ, one_mul]
      · rw [if_neg (Ne.symm h), zero_add]
        apply sum_single _ (τ ∪ τ')
        · intro σ hσ
          obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := Finset.mem_filter.mp hσ
          exact union_eq τ τ' σ h1 h3 h2 h4 h
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hX', ⟨-, h2⟩, h3, h4⟩
            exact ⟨by omega, h, hX', h2⟩
          · rintro ⟨h1, -, h3, h4⟩
            exact ⟨h3, ⟨Finset.subset_union_left, h4⟩, Finset.subset_union_right, by omega⟩
    rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib, Finset.sum_ite_eq X τ (fun _ => φ τ),
      if_pos hτX, ← Finset.sum_filter]
    unfold upperWalk
    rw [if_pos hτX, mul_add, Finset.mul_sum, hcard]
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    congr 1
    · field_simp
    · apply Finset.sum_congr
      · apply Finset.filter_congr
        intro x _
        tauto
      · intro x _
        field_simp
  · obtain ⟨hτX, hτc⟩ := Finset.mem_filter.mp hτ
    have hcard : ((τ.card : ℕ) : ℝ) = (k : ℝ) + 1 := by rw [hτc]; push_cast; ring
    unfold dS
    rw [if_pos hτX]
    have hdst : ∀ η ∈ X.filter (fun η => η ⊆ τ ∧ η.card + 1 = τ.card),
        dStar X m φ η =
          ∑ τ' ∈ X.filter (fun τ' => η ⊆ τ' ∧ τ'.card = η.card + 1), m τ' / m η * φ τ' := by
      intro η hη
      unfold dStar
      rw [if_pos (Finset.mem_filter.mp hη).1]
    rw [Finset.sum_congr rfl hdst]
    rw [Finset.sum_comm' (t' := X) (s' := fun τ' => X.filter (fun η =>
      (η ⊆ τ ∧ η.card + 1 = τ.card) ∧ (η ⊆ τ' ∧ τ'.card = η.card + 1)))
      (by intro x y; simp only [Finset.mem_filter]; tauto)]
    have hg : ∀ τ' ∈ X, ∑ η ∈ X.filter (fun η =>
        (η ⊆ τ ∧ η.card + 1 = τ.card) ∧ (η ⊆ τ' ∧ τ'.card = η.card + 1)), m τ' / m η * φ τ' =
        (if τ = τ' then ∑ η ∈ X.filter (fun η => η ⊆ τ ∧ η.card + 1 = τ.card),
            m τ / m η * φ τ else 0) +
          (if (τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∩ τ' ∈ X ∧ (τ ∩ τ').card + 1 = τ.card) then
            m τ' / m (τ ∩ τ') * φ τ' else 0) := by
      intro τ' hτ'X
      by_cases h : τ' = τ
      · subst h
        rw [if_pos rfl, if_neg (by tauto), add_zero]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        exact Finset.filter_congr (fun η _ => ⟨fun ⟨h, _⟩ => h,
          fun ⟨a, b⟩ => ⟨⟨a, b⟩, a, b.symm⟩⟩)
      · rw [if_neg (Ne.symm h), zero_add]
        apply sum_single _ (τ ∩ τ')
        · intro η hη
          obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := Finset.mem_filter.mp hη
          exact inter_eq τ τ' η h1 h3 h2 h4 h
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hX', ⟨-, h2⟩, -, h4⟩
            exact ⟨by omega, h, hX', h2⟩
          · rintro ⟨h1, -, h3, h4⟩
            exact ⟨h3, ⟨Finset.inter_subset_left, h4⟩, Finset.inter_subset_right, by omega⟩
    rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib, Finset.sum_ite_eq X τ,
      if_pos hτX, ← Finset.sum_filter]
    unfold lowerWalk
    rw [if_pos hτX, mul_add, Finset.mul_sum, hcard]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    congr 1
    · rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η hη
      have : m η ≠ 0 := (hm.1 η (Finset.mem_filter.mp hη).1).ne'
      field_simp
    · apply Finset.sum_congr
      · apply Finset.filter_congr
        intro x _
        tauto
      · intro x hx
        have : m (τ ∩ x) ≠ 0 := (hm.1 _ (Finset.mem_filter.mp hx).2.2.2.1).ne'
        field_simp
