-- Prove2me | solution 1 for HighOrderWalks.TwoSided.proposition_4_1_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:58:45.857832+00:00
-- url     : https://prove2.me/submissions/5c510bf5-1363-4529-8b33-7412bc62158c

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

/- Supporting incidence helpers adapted from Nickrobbins95, accepted submission f3347acc-2e62-4054-8da8-fa7228623546. -/
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


end HOW54


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

theorem HighOrderWalks.OneSided.proposition_4_1_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
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



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLocalInner WalksLocalAdjoint

namespace WalksLocalDifferential

variable {V : Type*} [DecidableEq V]

lemma energy_expansion {X : Finset (Finset V)} {m : Finset V → ℝ} {k : ℕ}
    (hbal : ∀ σ ∈ cells X (k + 1), (∑ ρ ∈ U X σ, m ρ) = m σ)
    (φ ψ : Finset V → ℝ) :
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
  · have hw : ∑ ρ ∈ U X σ, m ρ = m σ := hbal σ hσ
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

lemma link_pairs {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    (τ : Finset V) (φ ψ : Finset V → ℝ) :
    (∑ η ∈ cells (link X τ) 1, ∑ η' ∈ W (link X τ) η,
      linkWeight m τ (η ∪ η') * loc φ τ η' * loc ψ τ η) =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * φ σ' * ψ σ := by
  rw [← B1 hdc]
  apply Finset.sum_congr rfl
  intro η hη
  rw [← B2 hdc hη]
  apply Finset.sum_congr rfl
  intro η' _
  simp only [linkWeight, loc]
  have hu : τ ∪ η ∪ (τ ∪ η') = τ ∪ (η ∪ η') := by
    ext x
    simp only [Finset.mem_union]
    tauto
  rw [hu]

lemma link_balance {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n)
    {m : Finset V → ℝ} (hm : IsWeight X n m) {l : ℕ} (hl : l < n)
    {τ : Finset V} (hτ : τ ∈ cells X l) {η : Finset V} (hη : η ∈ cells (link X τ) 1) :
    (∑ σ ∈ U (link X τ) η, linkWeight m τ σ) = linkWeight m τ η := by
  have hηL := (Finset.mem_filter.mp hη).1
  change (∑ σ ∈ U (link X τ) η, m (τ ∪ σ)) = m (τ ∪ η)
  rw [link_up_sum hX.1 τ η hηL]
  have hη' := Finset.mem_filter.mp hηL
  have hc : (τ ∪ η).card ≤ n := by
    rw [Finset.card_union_eq_card_add_card.mpr hη'.2.1,
      (Finset.mem_filter.mp hτ).2, (Finset.mem_filter.mp hη).2]
    omega
  exact (hm.2 _ hη'.2.2 hc).symm

end WalksLocalDifferential

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (l : ℕ) (hl : l < n) (φ ψ : Finset V → ℝ) :
    ip X m (l + 2) (dS X φ) (dS X ψ) =
      ∑ τ ∈ cells X l,
        (ip (link X τ) (linkWeight m τ) 2 (dS (link X τ) (loc φ τ)) (dS (link X τ) (loc ψ τ)) -
          (l : ℝ) / ((l : ℝ) + 1) * ip (link X τ) (linkWeight m τ) 1 (loc φ τ) (loc ψ τ)) := by
  have he (τ : Finset V) (hτ : τ ∈ cells X l) :
      ip (link X τ) (linkWeight m τ) 2 (dS (link X τ) (loc φ τ)) (dS (link X τ) (loc ψ τ)) =
        ip (link X τ) (linkWeight m τ) 1 (loc φ τ) (loc ψ τ) +
          ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
            m (σ ∪ σ') * φ σ' * ψ σ := by
    have h := WalksLocalDifferential.energy_expansion (k := 0)
      (fun η hη => WalksLocalDifferential.link_balance hX hm hl hτ hη) (loc φ τ) (loc ψ τ)
    rw [WalksLocalDifferential.link_pairs hX.1] at h
    exact h
  have hsum : (∑ τ ∈ cells X l,
      ip (link X τ) (linkWeight m τ) 1 (loc φ τ) (loc ψ τ)) =
      ((l : ℝ) + 1) * ip X m (l + 1) φ ψ := by
    have h := WalksLocalInner.local_inner hX.1 m l (l + 1) (by omega) φ ψ
    simpa only [Nat.add_sub_cancel_left, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one] using h.symm
  calc
    _ = ip X m (l + 1) φ ψ +
        ∑ σ ∈ cells X (l + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ :=
      key1a hX hm (by omega) φ ψ
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have heSum := Finset.sum_congr rfl he
      rw [heSum, Finset.sum_add_distrib, G2 hX.1 l, hsum]
      have hn : (l : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring



#print axioms solution
