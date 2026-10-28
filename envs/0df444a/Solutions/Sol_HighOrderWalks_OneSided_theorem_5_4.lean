-- Prove2me | solution 1 for HighOrderWalks.OneSided.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T14:26:17.301235+00:00
-- url     : https://prove2.me/submissions/f3347acc-2e62-4054-8da8-fa7228623546

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

set_option autoImplicit false

namespace HOW54

open HighOrderWalks.OneSided Finset

variable {V : Type*} [DecidableEq V]

/-- faces one vertex above `σ` -/
def U (X : Finset (Finset V)) (σ : Finset V) : Finset (Finset V) :=
  X.filter (fun ρ => ρ.card = σ.card + 1 ∧ σ ⊆ ρ)

/-- faces one vertex below `ρ` -/
def D (X : Finset (Finset V)) (ρ : Finset V) : Finset (Finset V) :=
  X.filter (fun τ => τ ⊆ ρ ∧ τ.card + 1 = ρ.card)

/-- upper neighbours of `σ` -/
def W (X : Finset (Finset V)) (σ : Finset V) : Finset (Finset V) :=
  X.filter (fun σ' => σ'.card = σ.card ∧ σ' ≠ σ ∧ σ ∪ σ' ∈ X ∧ (σ ∪ σ').card = σ.card + 1)

theorem exch (X : Finset (Finset V)) (k : ℕ) (F : Finset V → Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, F τ σ = ∑ σ ∈ cells X (k + 1), ∑ τ ∈ D X σ, F τ σ := by
  apply Finset.sum_comm'
  intro τ σ
  simp only [cells, U, D, mem_filter]
  constructor
  · rintro ⟨⟨hτ, hk⟩, hσ, hc, hsub⟩
    exact ⟨⟨hτ, hsub, by omega⟩, hσ, by omega⟩
  · rintro ⟨⟨hτ, hsub, hc⟩, hσ, hk⟩
    exact ⟨⟨hτ, by omega⟩, hσ, by omega, hsub⟩

theorem card_D {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {σ : Finset V}
    (hσ : σ ∈ X) {k : ℕ} (hk : σ.card = k + 1) : (D X σ).card = k + 1 := by
  have : D X σ = σ.powersetCard k := by
    ext τ
    simp only [D, mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hdc σ hσ τ h1, h1, by omega⟩
  rw [this, card_powersetCard, hk, Nat.choose_succ_self_right]

theorem sumU {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (k : ℕ)
    (F : Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, F σ = ((k : ℝ) + 1) * ∑ σ ∈ cells X (k + 1), F σ := by
  rw [exch X k (fun _ σ => F σ), mul_sum]
  apply sum_congr rfl
  intro σ hσ
  simp only [cells, mem_filter] at hσ
  rw [sum_const, card_D hdc hσ.1 hσ.2, nsmul_eq_mul]
  push_cast
  ring

theorem union_eq {σ σ' ρ : Finset V} (h1 : σ ⊆ ρ) (h2 : σ' ⊆ ρ) (hc : σ'.card = σ.card)
    (hne : σ' ≠ σ) (hρ : ρ.card = σ.card + 1) : σ ∪ σ' = ρ := by
  apply Finset.eq_of_subset_of_card_le (Finset.union_subset h1 h2)
  rw [hρ]
  have hss : σ ⊂ σ ∪ σ' := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
    intro heq
    apply hne
    have : σ' ⊆ σ := by
      calc σ' ⊆ σ ∪ σ' := Finset.subset_union_right
        _ = σ := heq.symm
    exact Finset.eq_of_subset_of_card_le this (by omega)
  have := Finset.card_lt_card hss
  omega

theorem key1a {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {k : ℕ} (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    ip X m (k + 1 + 1) (dS X φ) (dS X ψ) =
      ∑ σ ∈ cells X (k + 1), m σ * φ σ * ψ σ +
        ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ := by
  have hL : ip X m (k + 1 + 1) (dS X φ) (dS X ψ) =
      ∑ ρ ∈ cells X (k + 1 + 1), ∑ σ ∈ D X ρ, (m ρ * φ σ * ψ σ +
        ∑ σ' ∈ (D X ρ).erase σ, m ρ * φ σ' * ψ σ) := by
    unfold ip
    apply sum_congr rfl
    intro ρ hρ
    have hρX : ρ ∈ X := (mem_filter.mp hρ).1
    have e1 : dS X φ ρ = ∑ τ ∈ D X ρ, φ τ := by simp only [dS, if_pos hρX, D]
    have e2 : dS X ψ ρ = ∑ τ ∈ D X ρ, ψ τ := by simp only [dS, if_pos hρX, D]
    have : ∀ σ ∈ D X ρ, m ρ * φ σ * ψ σ + ∑ σ' ∈ (D X ρ).erase σ, m ρ * φ σ' * ψ σ
        = (m ρ * ∑ τ ∈ D X ρ, φ τ) * ψ σ := by
      intro σ hσ
      rw [Finset.add_sum_erase _ (fun σ' => m ρ * φ σ' * ψ σ) hσ, Finset.mul_sum, Finset.sum_mul]
    rw [sum_congr rfl this, ← Finset.mul_sum, e1, e2]
  rw [hL, ← exch X (k + 1), ← sum_add_distrib]
  apply sum_congr rfl
  intro σ hσ
  have hσ' := mem_filter.mp hσ
  rw [sum_add_distrib]
  congr 1
  · have hw : ∑ ρ ∈ U X σ, m ρ = m σ := (hm.2 σ hσ'.1 (by omega)).symm
    rw [← sum_mul, ← sum_mul, hw]
  · rw [Finset.sum_comm' (t' := W X σ) (s' := fun σ' => {σ ∪ σ'})]
    · simp only [sum_singleton]
    · intro ρ σ'
      simp only [U, D, W, mem_filter, mem_erase, mem_singleton]
      constructor
      · rintro ⟨⟨hρX, hρc, hσρ⟩, hne, hσ'X, hσ'ρ, hσ'c⟩
        have hu := union_eq hσρ hσ'ρ (by omega) hne hρc
        refine ⟨hu.symm, hσ'X, by omega, hne, by rw [hu]; exact hρX, by rw [hu]; exact hρc⟩
      · rintro ⟨rfl, hσ'X, hc, hne, hu, huc⟩
        exact ⟨⟨hu, huc, subset_union_left⟩, hne, hσ'X, subset_union_right, by omega⟩

theorem key1b {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) {k : ℕ} (φ ψ : Finset V → ℝ) :
    ((k : ℝ) + 1 + 1) * ip X m (k + 1) (upperWalk X m φ) ψ =
      ∑ σ ∈ cells X (k + 1), m σ * φ σ * ψ σ +
        ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ := by
  unfold ip
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro σ hσ
  simp only [cells, mem_filter] at hσ
  obtain ⟨hσX, hσc⟩ := hσ
  have hmσ : m σ ≠ 0 := (hm.1 σ hσX).ne'
  have hc : ((σ.card : ℕ) : ℝ) + 1 = (k : ℝ) + 1 + 1 := by rw [hσc]; push_cast; ring
  have h2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
  have hu : upperWalk X m φ σ = φ σ / ((k : ℝ) + 1 + 1) +
      ∑ σ' ∈ W X σ, m (σ ∪ σ') / (((k : ℝ) + 1 + 1) * m σ) * φ σ' := by
    simp only [upperWalk, if_pos hσX, hc, W]
  have hs : ∑ σ' ∈ W X σ, m (σ ∪ σ') / (((k : ℝ) + 1 + 1) * m σ) * φ σ' =
      (∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ') / (((k : ℝ) + 1 + 1) * m σ) := by
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro σ' _
    ring
  rw [hu, hs, ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

theorem B1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {τ : Finset V}
    (F : Finset V → ℝ) :
    ∑ η ∈ cells (link X τ) 1, F (τ ∪ η) = ∑ σ ∈ U X τ, F σ := by
  apply Finset.sum_nbij' (fun η => τ ∪ η) (fun σ => σ \ τ)
  · intro η hη
    simp only [cells, link, U, mem_filter] at hη ⊢
    obtain ⟨⟨-, hd, hu⟩, h1⟩ := hη
    exact ⟨hu, by rw [card_union_eq_card_add_card.mpr hd, h1], subset_union_left⟩
  · intro σ hσ
    simp only [cells, link, U, mem_filter] at hσ ⊢
    obtain ⟨hσX, hc, hsub⟩ := hσ
    refine ⟨⟨hdc σ hσX _ sdiff_subset, disjoint_sdiff, ?_⟩, ?_⟩
    · rw [union_sdiff_of_subset hsub]; exact hσX
    · have := card_sdiff_add_card_eq_card hsub; omega
  · intro η hη
    simp only [cells, link, mem_filter] at hη
    exact union_sdiff_cancel_left hη.1.2.1
  · intro σ hσ
    simp only [U, mem_filter] at hσ
    exact union_sdiff_of_subset hσ.2.2
  · intro η _
    rfl

theorem B2 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {τ η : Finset V}
    (hη : η ∈ cells (link X τ) 1) (F : Finset V → ℝ) :
    ∑ η' ∈ W (link X τ) η, F (τ ∪ η') =
      ∑ σ' ∈ (W X (τ ∪ η)).filter (fun σ' => τ ⊆ σ'), F σ' := by
  simp only [cells, link, mem_filter] at hη
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη
  have hcη : (τ ∪ η).card = τ.card + 1 := by rw [card_union_eq_card_add_card.mpr hdη, hη1]
  apply Finset.sum_nbij' (fun η' => τ ∪ η') (fun σ' => σ' \ τ)
  · intro η' h
    simp only [W, link, mem_filter] at h ⊢
    obtain ⟨⟨hη'X, hd', hu'⟩, hc', hne, ⟨hUX, hdU, huU⟩, hcU⟩ := h
    have e : τ ∪ η ∪ (τ ∪ η') = τ ∪ (η ∪ η') := by
      ext x; simp only [mem_union]; tauto
    refine ⟨⟨hu', ?_, ?_, ?_, ?_⟩, subset_union_left⟩
    · rw [card_union_eq_card_add_card.mpr hd']; omega
    · intro h; apply hne
      have h' : (τ ∪ η') \ τ = (τ ∪ η) \ τ := by rw [h]
      rwa [union_sdiff_cancel_left hd', union_sdiff_cancel_left hdη] at h'
    · rw [e]; exact huU
    · rw [e, card_union_eq_card_add_card.mpr hdU]; omega
  · intro σ' h
    simp only [W, link, mem_filter] at h ⊢
    obtain ⟨⟨hσ'X, hc', hne, hUX, hcU⟩, hsub⟩ := h
    have e1 : τ ∪ (σ' \ τ) = σ' := union_sdiff_of_subset hsub
    have e2 : τ ∪ (η ∪ σ' \ τ) = τ ∪ η ∪ σ' := by
      ext x; simp only [mem_union, mem_sdiff]; have := @hsub x; tauto
    have hdA : Disjoint τ (η ∪ σ' \ τ) := disjoint_union_right.mpr ⟨hdη, disjoint_sdiff⟩
    have hcs : (σ' \ τ).card + τ.card = σ'.card := card_sdiff_add_card_eq_card hsub
    refine ⟨⟨hdc σ' hσ'X _ sdiff_subset, disjoint_sdiff, by rw [e1]; exact hσ'X⟩, by omega, ?_,
      ⟨?_, hdA, by rw [e2]; exact hUX⟩, ?_⟩
    · intro h; apply hne; rw [← e1, h]
    · exact hdc _ hUX _ (by rw [← e2]; exact subset_union_right)
    · have := card_union_eq_card_add_card.mpr hdA
      rw [e2, hcU, hcη] at this
      omega
  · intro η' h
    simp only [W, link, mem_filter] at h
    exact union_sdiff_cancel_left h.1.2.1
  · intro σ' h
    simp only [mem_filter] at h
    exact union_sdiff_of_subset h.2
  · intro _ _
    rfl

theorem link1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X)
    {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ) {τ : Finset V} (f : Finset V → ℝ) :
    ip (link X τ) (linkWeight m τ) 1 (nonLazyWalk (link X τ) (linkWeight m τ) (loc f τ))
        (loc f τ) =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * f σ := by
  unfold ip
  rw [← B1 hdc (fun σ => ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * f σ)]
  apply sum_congr rfl
  intro η hη
  have hη' := hη
  simp only [cells, link, mem_filter] at hη'
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη'
  have hηL : η ∈ link X τ := mem_filter.mpr ⟨hηX, hdη, huη⟩
  have hw : linkWeight m τ η ≠ 0 := (hpos _ huη).ne'
  have hc : ((η.card : ℕ) : ℝ) = 1 := by rw [hη1]; norm_num
  rw [← B2 hdc hη (fun σ' => m (τ ∪ η ∪ σ') * f σ' * f (τ ∪ η))]
  have e : ∀ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) = linkWeight m τ (η ∪ η') := by
    intro η' _
    simp only [linkWeight]
    congr 1
    ext x; simp only [mem_union]; tauto
  have e' : ∑ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) * f (τ ∪ η') * f (τ ∪ η) =
      ∑ η' ∈ W (link X τ) η, linkWeight m τ (η ∪ η') * loc f τ η' * loc f τ η :=
    sum_congr rfl (fun η' h => by simp only [e η' h, loc])
  rw [e']
  simp only [nonLazyWalk, upperWalk, if_pos hηL, hc, W, div_mul_eq_mul_div, ← Finset.sum_div,
    ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

theorem inter_eq {X : Finset (Finset V)} {τ σ σ' : Finset V} (hσ : σ ∈ U X τ)
    (hσ' : σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ')) : σ ∩ σ' = τ := by
  simp only [U, W, mem_filter] at hσ hσ'
  obtain ⟨hσX, hσc, hτσ⟩ := hσ
  obtain ⟨⟨hX', hc', hne, hu, huc⟩, hτσ'⟩ := hσ'
  have := card_union_add_card_inter σ σ'
  exact (Finset.eq_of_subset_of_card_le (subset_inter hτσ hτσ') (by omega)).symm

theorem R1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {n : ℕ}
    {m : Finset V → ℝ} (hm : IsWeight X n m) {τ σ : Finset V} (hσ : σ ∈ U X τ)
    (hn : σ.card ≤ n) :
    ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') = m σ := by
  have hσ0 := hσ
  simp only [U, mem_filter] at hσ0
  obtain ⟨hσX, hσc, hτσ⟩ := hσ0
  have hw : m σ = ∑ ρ ∈ U X σ, m ρ := hm.2 σ hσX hn
  rw [hw]
  have hcd : (σ \ τ).card = 1 := by have := card_sdiff_add_card_eq_card hτσ; omega
  apply Finset.sum_nbij' (fun σ' => σ ∪ σ') (fun ρ => ρ \ (σ \ τ))
  · intro σ' h
    have h0 := h
    simp only [W, mem_filter] at h0
    simp only [U, mem_filter]
    exact ⟨h0.1.2.2.2.1, h0.1.2.2.2.2, subset_union_left⟩
  · intro ρ h
    simp only [U, mem_filter] at h
    obtain ⟨hρX, hρc, hσρ⟩ := h
    have e : σ ∪ ρ \ (σ \ τ) = ρ := by
      ext x; simp only [mem_union, mem_sdiff]; have := @hσρ x; tauto
    have hsub : σ \ τ ⊆ ρ := sdiff_subset.trans hσρ
    have hc2 := card_sdiff_add_card_eq_card hsub
    simp only [W, mem_filter]
    refine ⟨⟨hdc ρ hρX _ sdiff_subset, by omega, ?_, by rw [e]; exact hρX, by rw [e]; exact hρc⟩, ?_⟩
    · intro h
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (σ \ τ).card)
      have hxσ : x ∈ σ := (mem_sdiff.mp hx).1
      rw [← h] at hxσ
      exact (mem_sdiff.mp hxσ).2 hx
    · intro x hx
      exact mem_sdiff.mpr ⟨hσρ (hτσ hx), fun h => (mem_sdiff.mp h).2 hx⟩
  · intro σ' h
    have hi := inter_eq hσ h
    have h0 := h
    simp only [mem_filter] at h0
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro ⟨hx | hx, hnx⟩
      · by_cases hxτ : x ∈ τ
        · exact h0.2 hxτ
        · exact absurd ⟨hx, hxτ⟩ hnx
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_⟩
      rintro ⟨hxσ, hxτ⟩
      apply hxτ
      rw [← hi]
      exact mem_inter.mpr ⟨hxσ, hx⟩
  · intro ρ h
    simp only [U, mem_filter] at h
    have hs2 := h.2.2
    ext x; simp only [mem_union, mem_sdiff]; have := @hs2 x; tauto
  · intro _ _
    rfl

theorem SYM {X : Finset (Finset V)} {τ : Finset V} (H : Finset V → Finset V → ℝ) :
    ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), H σ σ' =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), H σ' σ := by
  rw [Finset.sum_comm' (t' := U X τ) (s' := fun σ' => (W X σ').filter (fun σ => τ ⊆ σ))]
  intro σ σ'
  simp only [U, W, mem_filter]
  constructor
  · rintro ⟨⟨hX, hc, hτ⟩, ⟨hX', hc', hne, hu, huc⟩, hτ'⟩
    exact ⟨⟨⟨hX, by omega, fun h => hne h.symm, by rw [union_comm]; exact hu,
      by rw [union_comm]; omega⟩, hτ⟩, hX', by omega, hτ'⟩
  · rintro ⟨⟨⟨hX, hc, hne, hu, huc⟩, hτ⟩, hX', hc', hτ'⟩
    exact ⟨⟨hX, by omega, hτ⟩, ⟨hX', by omega, fun h => hne h.symm, by rw [union_comm]; exact hu,
      by rw [union_comm]; omega⟩, hτ'⟩

theorem G2 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (k : ℕ)
    (G : Finset V → Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), G σ σ' =
      ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, G σ σ' := by
  rw [exch X k]
  apply sum_congr rfl
  intro σ hσ
  have hσX : σ ∈ X := (mem_filter.mp hσ).1
  rw [Finset.sum_comm' (t' := W X σ) (s' := fun σ' => (D X σ).filter (fun τ => τ ⊆ σ'))]
  · apply sum_congr rfl
    intro σ' hσ'
    have hs : (D X σ).filter (fun τ => τ ⊆ σ') = {σ ∩ σ'} := by
      have h0 := hσ'
      simp only [W, mem_filter] at h0
      obtain ⟨hX', hc', hne, hu, huc⟩ := h0
      have hcu := card_union_add_card_inter σ σ'
      ext τ
      simp only [D, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨hτX, hτσ, hτc⟩, hτσ'⟩
        exact Finset.eq_of_subset_of_card_le (subset_inter hτσ hτσ') (by omega)
      · rintro rfl
        exact ⟨⟨hdc σ hσX _ inter_subset_left, inter_subset_left, by omega⟩, inter_subset_right⟩
    rw [hs, sum_singleton]
  · intro τ σ'
    simp only [mem_filter]
    tauto

theorem ip_nonneg {X : Finset (Finset V)} {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ)
    (c : ℕ) (f : Finset V → ℝ) : 0 ≤ ip X m c f f := by
  unfold ip
  apply sum_nonneg
  intro σ hσ
  have := hpos σ (mem_filter.mp hσ).1
  rw [mul_assoc]
  exact mul_nonneg this.le (mul_self_nonneg _)

theorem ip_cs {X : Finset (Finset V)} {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ)
    (c : ℕ) (f g : Finset V → ℝ) :
    (ip X m c f g) ^ 2 ≤ ip X m c f f * ip X m c g g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (cells X c) (fun σ => Real.sqrt (m σ) * f σ)
    (fun σ => Real.sqrt (m σ) * g σ)
  have hm' : ∀ σ ∈ cells X c, Real.sqrt (m σ) ^ 2 = m σ :=
    fun σ hσ => Real.sq_sqrt (hpos σ (mem_filter.mp hσ).1).le
  have e1 : ∑ σ ∈ cells X c, Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ) = ip X m c f g := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [show Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ) = Real.sqrt (m σ) ^ 2 * f σ * g σ by
      ring, hm' σ hσ]
  have e2 : ∑ σ ∈ cells X c, (Real.sqrt (m σ) * f σ) ^ 2 = ip X m c f f := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [mul_pow, hm' σ hσ]; ring
  have e3 : ∑ σ ∈ cells X c, (Real.sqrt (m σ) * g σ) ^ 2 = ip X m c g g := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [mul_pow, hm' σ hσ]; ring
  calc (ip X m c f g) ^ 2
      = (∑ σ ∈ cells X c, Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ)) ^ 2 := by rw [e1]
    _ ≤ (∑ σ ∈ cells X c, (Real.sqrt (m σ) * f σ) ^ 2) *
          ∑ σ ∈ cells X c, (Real.sqrt (m σ) * g σ) ^ 2 := h
    _ = ip X m c f f * ip X m c g g := by rw [e2, e3]

theorem ADJ (X : Finset (Finset V)) (m : Finset V → ℝ) (k : ℕ) (φ ψ : Finset V → ℝ) :
    ∑ σ ∈ cells X (k + 1), m σ * φ σ * dS X ψ σ =
      ∑ τ ∈ cells X k, ψ τ * ∑ σ ∈ U X τ, m σ * φ σ := by
  simp only [Finset.mul_sum]
  rw [exch X k]
  apply sum_congr rfl
  intro σ hσ
  have hσX : σ ∈ X := (mem_filter.mp hσ).1
  simp only [dS, if_pos hσX, Finset.mul_sum, D]
  apply sum_congr rfl
  intro τ _
  ring

theorem local_ineq {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} {k : ℕ} (hk : k + 1 ≤ n)
    (hlink : LinkUpper X m k lam) {τ : Finset V} (hτ : τ ∈ cells X k) (φ : Finset V → ℝ) :
    ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ ≤
      lam * ∑ σ ∈ U X τ, m σ * φ σ * φ σ +
        (1 - lam) * ((∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ) := by
  have hdc := hX.1
  have hpos := hm.1
  have hτ0 := mem_filter.mp hτ
  have hτX : τ ∈ X := hτ0.1
  have hτc : τ.card = k := hτ0.2
  have hmτ : 0 < m τ := hpos τ hτX
  have hwτ : ∑ σ ∈ U X τ, m σ = m τ := (hm.2 τ hτX (by omega)).symm
  have hσn : ∀ σ ∈ U X τ, σ.card ≤ n := by
    intro σ hσ
    have := (mem_filter.mp hσ).2.1
    omega
  have hR1 : ∀ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') = m σ :=
    fun σ hσ => R1 hdc hm hσ (hσn σ hσ)
  obtain ⟨A, hA⟩ : ∃ A, ∑ σ ∈ U X τ, m σ * φ σ = A := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = A / m τ := ⟨_, rfl⟩
  have hamτ : a * m τ = A := by rw [ha, div_mul_cancel₀ A hmτ.ne']
  rw [hA]
  have horth : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ) (fun _ => 1) = 0 := by
    have e : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ) (fun _ => 1) =
        ∑ σ ∈ U X τ, m σ * (φ σ - a) * 1 := B1 hdc (fun σ => m σ * (φ σ - a) * 1)
    rw [e]
    have : ∀ σ ∈ U X τ, m σ * (φ σ - a) * 1 = m σ * φ σ - a * m σ := fun _ _ => by ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, hA, hwτ, hamτ, sub_self]
  have hle := hlink τ hτ (loc (fun σ => φ σ - a) τ) horth
  rw [link1 hdc hpos (fun σ => φ σ - a)] at hle
  have e2 : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ)
      (loc (fun σ => φ σ - a) τ) = ∑ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) :=
    B1 hdc (fun σ => m σ * (φ σ - a) * (φ σ - a))
  rw [e2] at hle
  have hC : ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' = A := by
    rw [SYM (fun σ σ' => m (σ ∪ σ') * φ σ'), ← hA]
    apply sum_congr rfl
    intro σ hσ
    rw [← sum_mul, ← hR1 σ hσ]
    congr 1
    apply sum_congr rfl
    intro σ' _
    rw [union_comm]
  have hL : ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * (φ σ' - a) * (φ σ - a) =
      (∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ)
        - a * A - a * A + a ^ 2 * m τ := by
    calc ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
          m (σ ∪ σ') * (φ σ' - a) * (φ σ - a)
        = ∑ σ ∈ U X τ, (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ
            - a * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ'
            - a * φ σ * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')
            + a ^ 2 * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')) := by
          apply sum_congr rfl
          intro σ _
          simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
          apply sum_congr rfl
          intro σ' _
          ring
      _ = ∑ σ ∈ U X τ, (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ
            - a * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ'
            - a * (m σ * φ σ) + a ^ 2 * m σ) := by
          apply sum_congr rfl
          intro σ hσ
          rw [hR1 σ hσ]
          ring
      _ = _ := by
          rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
            hC, hA, hwτ]
  have hS : ∑ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) =
      (∑ σ ∈ U X τ, m σ * φ σ * φ σ) - a * A - a * A + a ^ 2 * m τ := by
    have : ∀ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) =
        m σ * φ σ * φ σ - a * (m σ * φ σ) - a * (m σ * φ σ) + a ^ 2 * m σ := fun _ _ => by ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
      ← mul_sum, hA, hwτ]
  rw [hL, hS] at hle
  have e1 : A ^ 2 / m τ = a * A := by
    rw [← hamτ]
    first
      | (field_simp; ring)
      | field_simp
  have e3 : a ^ 2 * m τ = a * A := by rw [← hamτ]; ring
  have e4 : lam * (a ^ 2 * m τ) = lam * (a * A) := by rw [e3]
  rw [e1]
  nlinarith [hle, e3, e4]

theorem step {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hexp : OneSidedLSE X m n lam) {k : ℕ} (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (C : ℝ)
    (hB : ∑ τ ∈ cells X k, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ ≤ C * ip X m (k + 1) φ φ) :
    ip X m (k + 1 + 1) (dS X φ) (dS X φ) ≤
      (1 + lam * ((k : ℝ) + 1) + C) * ip X m (k + 1) φ φ := by
  have hdc := hX.1
  have hE := key1a hX hm hk φ φ
  rw [← G2 hdc k (fun σ σ' => m (σ ∪ σ') * φ σ' * φ σ)] at hE
  have hT := sum_le_sum (fun τ (hτ : τ ∈ cells X k) => local_ineq hX hm hk (hexp k hk) hτ φ)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sumU hdc k (fun σ => m σ * φ σ * φ σ)] at hT
  have hB0 : 0 ≤ ∑ τ ∈ cells X k, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ :=
    sum_nonneg (fun τ hτ => div_nonneg (sq_nonneg _) (hm.1 τ (mem_filter.mp hτ).1).le)
  have hN : ip X m (k + 1) φ φ = ∑ σ ∈ cells X (k + 1), m σ * φ σ * φ σ := rfl
  rw [hE]
  rw [hN] at hB ⊢
  have := mul_nonneg hlam0 hB0
  nlinarith [hT, hB, this]

theorem main_ind {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hexp : OneSidedLSE X m n lam) :
    ∀ k : ℕ, k + 1 ≤ n → ∀ φ : Finset V → ℝ, ip X m (k + 1) φ (fun _ => 1) = 0 →
      ip X m (k + 1 + 1) (dS X φ) (dS X φ) ≤
        ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * lam) * ip X m (k + 1) φ φ := by
  have hdc := hX.1
  intro k
  induction k with
  | zero =>
    intro hk φ hφ
    have hA0 : ∑ τ ∈ cells X 0, ∑ σ ∈ U X τ, m σ * φ σ = 0 := by
      rw [sumU hdc 0 (fun σ => m σ * φ σ)]
      have : ∑ σ ∈ cells X (0 + 1), m σ * φ σ = 0 := by
        rw [← hφ]
        unfold ip
        apply sum_congr rfl
        intro σ _
        simp only [mul_one]
      rw [this, mul_zero]
    have hsub : cells X 0 ⊆ {∅} := by
      intro τ hτ
      simp only [cells, mem_filter, card_eq_zero] at hτ
      exact mem_singleton.mpr hτ.2
    have hB : ∑ τ ∈ cells X 0, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ = 0 := by
      rcases subset_singleton_iff.mp hsub with h | h
      · rw [h, sum_empty]
      · rw [h, sum_singleton] at hA0 ⊢
        rw [hA0]
        simp
    refine le_trans (step hX hm hlam0 hlam1 hexp hk φ 0 (by rw [hB, zero_mul])) (le_of_eq ?_)
    push_cast
    ring
  | succ j ih =>
    intro hk φ hφ
    have hj : j + 1 ≤ n := by omega
    have hpos := hm.1
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Finset V → ℝ, ψ = fun τ => (∑ σ ∈ U X τ, m σ * φ σ) / m τ :=
      ⟨_, rfl⟩
    have hψ1 : ip X m (j + 1) ψ (fun _ => 1) = 0 := by
      unfold ip
      have : ∀ τ ∈ cells X (j + 1), m τ * ψ τ * (fun _ => (1:ℝ)) τ =
          ∑ σ ∈ U X τ, m σ * φ σ := by
        intro τ hτ
        have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
        rw [hψ]
        field_simp
      rw [sum_congr rfl this, sumU hdc (j + 1) (fun σ => m σ * φ σ)]
      have h0 : ∑ σ ∈ cells X (j + 1 + 1), m σ * φ σ = 0 := by
        rw [← hφ]
        unfold ip
        apply sum_congr rfl
        intro σ _
        simp only [mul_one]
      rw [h0, mul_zero]
    have hNψ : ip X m (j + 1) ψ ψ =
        ∑ τ ∈ cells X (j + 1), (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ := by
      unfold ip
      apply sum_congr rfl
      intro τ hτ
      have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
      rw [hψ]
      field_simp
    have hadj : ip X m (j + 1) ψ ψ = ip X m (j + 1 + 1) φ (dS X ψ) := by
      unfold ip
      rw [ADJ X m (j + 1) φ ψ]
      apply sum_congr rfl
      intro τ hτ
      have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
      rw [hψ]
      field_simp
    have hCS := ip_cs hpos (j + 1 + 1) φ (dS X ψ)
    rw [← hadj] at hCS
    have hih := ih hj ψ hψ1
    have hNψ0 := ip_nonneg hpos (j + 1) ψ
    have hNφ0 := ip_nonneg hpos (j + 1 + 1) φ
    have hCj0 : 0 ≤ (j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam :=
      add_nonneg (by positivity) (mul_nonneg (by positivity) hlam0)
    have hbound : ip X m (j + 1) ψ ψ ≤
        ((j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam) * ip X m (j + 1 + 1) φ φ := by
      rcases eq_or_lt_of_le hNψ0 with h0 | hp
      · rw [← h0]
        exact mul_nonneg hCj0 hNφ0
      · have h1 := mul_le_mul_of_nonneg_left hih hNφ0
        have : ip X m (j + 1) ψ ψ * ip X m (j + 1) ψ ψ ≤
            ((j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam) * ip X m (j + 1 + 1) φ φ *
              ip X m (j + 1) ψ ψ := by
          nlinarith [hCS, h1]
        exact le_of_mul_le_mul_right this hp
    refine le_trans (step hX hm hlam0 hlam1 hexp hk φ _ (by rw [← hNψ]; exact hbound))
      (le_of_eq ?_)
    push_cast
    ring

end HOW54

open HighOrderWalks.OneSided in
theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hexp : OneSidedLSE X m n lam)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0) :
    nrm X m (k + 1) (upperWalk X m φ) ≤
      (((k : ℝ) + 1) / ((k : ℝ) + 2) + ((k : ℝ) + 1) / 2 * lam) * nrm X m (k + 1) φ := by
  have hdc := hX.1
  have hpos := hm.1
  set u := upperWalk X m φ with hu
  set γ : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + 2) + ((k : ℝ) + 1) / 2 * lam with hγ
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hγ0 : 0 ≤ γ := add_nonneg (by positivity) (mul_nonneg (by positivity) hlam0)
  have hKγ : ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * lam) = ((k : ℝ) + 2) * γ := by
    rw [hγ]
    first
      | (field_simp; ring)
      | field_simp
  have hK0 : 0 ≤ ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * lam) := by
    rw [hKγ]; exact mul_nonneg hk2.le hγ0
  have hE : ∀ ψ, ip X m (k + 1 + 1) (dS X φ) (dS X ψ) = ((k : ℝ) + 1 + 1) * ip X m (k + 1) u ψ :=
    fun ψ => (HOW54.key1a hX hm hk φ ψ).trans (HOW54.key1b hm φ ψ).symm
  have hd1 : ∀ ρ ∈ cells X (k + 1 + 1), dS X (fun _ => (1 : ℝ)) ρ = (k : ℝ) + 1 + 1 := by
    intro ρ hρ
    have hρ' := Finset.mem_filter.mp hρ
    have : dS X (fun _ => (1 : ℝ)) ρ = ∑ τ ∈ HOW54.D X ρ, (1 : ℝ) := by
      simp only [dS, if_pos hρ'.1, HOW54.D]
    rw [this, Finset.sum_const, HOW54.card_D hdc hρ'.1 hρ'.2, nsmul_eq_mul, mul_one]
    norm_num
  have hu1 : ip X m (k + 1) u (fun _ => 1) = 0 := by
    have h1 := hE (fun _ => 1)
    have h2 : ip X m (k + 1 + 1) (dS X φ) (dS X (fun _ => (1 : ℝ))) =
        ((k : ℝ) + 1 + 1) * ∑ ρ ∈ cells X (k + 1 + 1), m ρ * 1 * dS X φ ρ := by
      unfold ip
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hd1 ρ hρ]
      ring
    rw [HOW54.ADJ X m (k + 1) (fun _ => 1) φ] at h2
    have h3 : ∑ σ ∈ cells X (k + 1), φ σ * ∑ ρ ∈ HOW54.U X σ, m ρ * 1 = 0 := by
      rw [← hφ]
      unfold ip
      apply Finset.sum_congr rfl
      intro σ hσ
      have hσ' := Finset.mem_filter.mp hσ
      have hw : ∑ ρ ∈ HOW54.U X σ, m ρ = m σ := (hm.2 σ hσ'.1 (by omega)).symm
      simp only [mul_one, hw]
      ring
    rw [h3, mul_zero] at h2
    rw [h2] at h1
    have : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left this
  have hφR := HOW54.main_ind hX hm hlam0 hlam1 hexp k hk φ hφ
  have huR := HOW54.main_ind hX hm hlam0 hlam1 hexp k hk u hu1
  have hCS := HOW54.ip_cs hpos (k + 1 + 1) (dS X φ) (dS X u)
  rw [hE u] at hCS
  have hNu0 := HOW54.ip_nonneg hpos (k + 1) u
  have hNφ0 := HOW54.ip_nonneg hpos (k + 1) φ
  have hEu0 := HOW54.ip_nonneg hpos (k + 1 + 1) (dS X u)
  have h0 := le_trans hCS (mul_le_mul hφR huR hEu0 (mul_nonneg hK0 hNφ0))
  rw [hKγ] at h0
  have h1 : ((k : ℝ) + 2) ^ 2 * (ip X m (k + 1) u u * ip X m (k + 1) u u) ≤
      ((k : ℝ) + 2) ^ 2 * ((γ ^ 2 * ip X m (k + 1) φ φ) * ip X m (k + 1) u u) := by
    have e : ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 := by ring
    rw [e] at h0
    nlinarith [h0]
  have h2 : ip X m (k + 1) u u * ip X m (k + 1) u u ≤
      (γ ^ 2 * ip X m (k + 1) φ φ) * ip X m (k + 1) u u :=
    le_of_mul_le_mul_left h1 (by positivity)
  have h3 : ip X m (k + 1) u u ≤ γ ^ 2 * ip X m (k + 1) φ φ := by
    rcases eq_or_lt_of_le hNu0 with h0' | hp
    · rw [← h0']
      exact mul_nonneg (sq_nonneg _) hNφ0
    · exact le_of_mul_le_mul_right h2 hp
  unfold nrm
  have := Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ0] at this
