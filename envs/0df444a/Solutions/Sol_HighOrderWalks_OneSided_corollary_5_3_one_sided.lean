-- Prove2me | solution 1 for HighOrderWalks.OneSided.corollary_5_3_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:09:57.14641+00:00
-- url     : https://prove2.me/submissions/426e89a4-59d0-483c-bc19-08d3d3205cea

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

/- Supporting lemmas from Nickrobbins95, accepted Prove2Me submission f3347acc-2e62-4054-8da8-fa7228623546. -/

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

open HighOrderWalks.OneSided HOW54 Finset

namespace WalksLaplacianIdentity

variable {V : Type*} [DecidableEq V]

lemma ip_single (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (f : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X c) :
    ip X m c f (Pi.single τ 1) = m τ * f τ := by
  classical
  simp [ip, Pi.single_apply, hτ]

lemma upper_identity (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (m : Finset V → ℝ) (hm : IsWeight X n m) (k : ℕ) (hk : k + 1 ≤ n)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X (k + 1)) :
    dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ := by
  classical
  have hτX := (Finset.mem_filter.mp hτ).1
  have hmτ : m τ ≠ 0 := (hm.1 τ hτX).ne'
  have h := (key1a hX hm hk φ (Pi.single τ 1)).trans
    (key1b hm φ (Pi.single τ 1)).symm
  rw [ip_single X m (k + 1) _ τ hτ] at h
  have hl : ip X m (k + 1 + 1) (dS X φ) (dS X (Pi.single τ 1)) =
      m τ * dStar X m (dS X φ) τ := by
    unfold ip
    rw [ADJ X m (k + 1)]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hτ, if_true]
    rw [dStar, if_pos hτX, Finset.mul_sum]
    apply Finset.sum_congr
    · ext σ
      simp [U, and_comm]
    · intro σ _
      field_simp
  rw [hl] at h
  apply (mul_left_cancel₀ hmτ)
  calc
    _ = ((k : ℝ) + 1 + 1) * (m τ * upperWalk X m φ τ) := h
    _ = _ := by ring

def L (X : Finset (Finset V)) (τ : Finset V) : Finset (Finset V) :=
  X.filter (fun τ' => τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∩ τ' ∈ X ∧
    (τ ∩ τ').card + 1 = τ.card)

lemma intersection_eq {η τ τ' : Finset V} (hητ : η ⊆ τ) (hητ' : η ⊆ τ')
    (hη : η.card + 1 = τ.card) (hc : τ'.card = τ.card) (hne : τ' ≠ τ) :
    τ ∩ τ' = η := by
  have hproper : τ ∩ τ' ⊂ τ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro he
    apply hne
    have hsub : τ ⊆ τ' := by rw [← he]; exact Finset.inter_subset_right
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hητ hητ')
    (by have h := Finset.card_lt_card hproper; omega)).symm

lemma lower_sum (X : Finset (Finset V)) (m : Finset V → ℝ)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ X) :
    dS X (dStar X m φ) τ =
      (∑ η ∈ D X τ, m τ / m η) * φ τ +
        ∑ τ' ∈ L X τ, m τ' / m (τ ∩ τ') * φ τ' := by
  classical
  have hl : dS X (dStar X m φ) τ =
      ∑ η ∈ D X τ, (m τ / m η * φ τ +
        ∑ τ' ∈ (U X η).erase τ, m τ' / m η * φ τ') := by
    rw [dS, if_pos hτ]
    change (∑ η ∈ D X τ, dStar X m φ η) = _
    apply Finset.sum_congr rfl
    intro η hη
    obtain ⟨hηX, hητ, hc⟩ := Finset.mem_filter.mp hη
    have hτU : τ ∈ U X η := Finset.mem_filter.mpr ⟨hτ, hc.symm, hητ⟩
    rw [Finset.add_sum_erase _ (fun τ' => m τ' / m η * φ τ') hτU, dStar, if_pos hηX]
    apply Finset.sum_congr
    · ext σ
      simp [U, and_comm]
    · intros; rfl
  rw [hl, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm' (t' := L X τ) (s' := fun τ' => {τ ∩ τ'})]
  · simp
  · intro η τ'
    simp only [D, U, L, Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hηX, hητ, hηc⟩, hne, hτ'X, hτ'c, hητ'⟩
      have hi := intersection_eq hητ hητ' hηc (by omega) hne
      refine ⟨hi.symm, hτ'X, by omega, hne, ?_, ?_⟩
      · rw [hi]; exact hηX
      · rw [hi]; exact hηc
    · rintro ⟨rfl, hτ'X, hc, hne, hiX, hic⟩
      exact ⟨⟨hiX, Finset.inter_subset_left, hic⟩, hne, hτ'X, by omega,
        Finset.inter_subset_right⟩

lemma lower_identity (X : Finset (Finset V)) (m : Finset V → ℝ) (k : ℕ)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X (k + 1)) :
    dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ := by
  classical
  obtain ⟨hτX, hτc⟩ := Finset.mem_filter.mp hτ
  have hc : (τ.card : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hτc
  have hn : (τ.card : ℝ) ≠ 0 := by rw [hc]; positivity
  rw [lower_sum X m φ τ hτX, ← hc, lowerWalk, if_pos hτX, mul_add, ← mul_assoc,
    Finset.mul_sum, Finset.mul_sum]
  change (∑ η ∈ D X τ, m τ / m η) * φ τ +
      ∑ τ' ∈ L X τ, m τ' / m (τ ∩ τ') * φ τ' =
    (∑ η ∈ D X τ, (τ.card : ℝ) * (m τ / ((τ.card : ℝ) * m η))) * φ τ +
      ∑ τ' ∈ L X τ, (τ.card : ℝ) * (m τ' / ((τ.card : ℝ) * m (τ ∩ τ')) * φ τ')
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro η _
    field_simp
  · apply Finset.sum_congr rfl
    intro τ' _
    field_simp

end WalksLaplacianIdentity

theorem HighOrderWalks.OneSided.corollary_3_7 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) :
    (∀ τ ∈ cells X (k + 1), dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ) ∧
      (∀ τ ∈ cells X (k + 1), dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ) := by
  exact ⟨WalksLaplacianIdentity.upper_identity X n hX m hm k hk φ,
    WalksLaplacianIdentity.lower_identity X m k φ⟩



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLocalInner WalksLocalAdjoint

namespace WalksLinkDecomposition

variable {V : Type*} [DecidableEq V]

lemma lower_link_constant {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    {τ : Finset V} (hτ : τ ∈ X) (φ : Finset V → ℝ)
    {η : Finset V} (hη : η ∈ cells (link X τ) 1) :
    lowerWalk (link X τ) (linkWeight m τ) (loc φ τ) η = dStar X m φ τ := by
  have he : (∅ : Finset V) ∈ link X τ := by
    simp only [link, mem_filter, Finset.disjoint_empty_right, union_empty, true_and]
    exact ⟨hdc τ hτ ∅ (empty_subset τ), hτ⟩
  have hD : D (link X τ) η = {∅} := by
    ext σ
    simp only [D, mem_filter, mem_singleton]
    constructor
    · intro h
      exact card_eq_zero.mp (by have := (mem_filter.mp hη).2; omega)
    · rintro rfl
      exact ⟨he, empty_subset η, by simpa using (mem_filter.mp hη).2.symm⟩
  have h := WalksLaplacianIdentity.lower_identity (link X τ) (linkWeight m τ) 0 (loc φ τ) η hη
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  rw [← h, dS, if_pos (mem_filter.mp hη).1]
  change (∑ σ ∈ D (link X τ) η, dStar (link X τ) (linkWeight m τ) (loc φ τ) σ) = _
  rw [hD, sum_singleton, local_dStar hdc m τ ∅ he φ, union_empty]

lemma nonLazy_congr {X : Finset (Finset V)} (m : Finset V → ℝ)
    {φ ψ : Finset V → ℝ} (hfg : ∀ η ∈ cells X 1, φ η = ψ η)
    {η : Finset V} (hη : η ∈ cells X 1) :
    nonLazyWalk X m φ η = nonLazyWalk X m ψ η := by
  have hηX := (mem_filter.mp hη).1
  have hηc := (mem_filter.mp hη).2
  simp only [nonLazyWalk, upperWalk, if_pos hηX, hfg η hη]
  congr 3
  apply sum_congr rfl
  intro η' hη'
  rw [hfg η' (mem_filter.mpr ⟨(mem_filter.mp hη').1, (mem_filter.mp hη').2.1.trans hηc⟩)]

lemma link_pairing {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X)
    {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ) {τ : Finset V} (f g : Finset V → ℝ) :
    ip (link X τ) (linkWeight m τ) 1 (nonLazyWalk (link X τ) (linkWeight m τ) (loc f τ))
        (loc g τ) =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * g σ := by
  unfold ip
  rw [← B1 hdc (fun σ => ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * g σ)]
  apply sum_congr rfl
  intro η hη
  have hη' := hη
  simp only [cells, link, mem_filter] at hη'
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη'
  have hηL : η ∈ link X τ := mem_filter.mpr ⟨hηX, hdη, huη⟩
  have hw : linkWeight m τ η ≠ 0 := (hpos _ huη).ne'
  have hc : ((η.card : ℕ) : ℝ) = 1 := by rw [hη1]; norm_num
  rw [← B2 hdc hη (fun σ' => m (τ ∪ η ∪ σ') * f σ' * g (τ ∪ η))]
  have e : ∀ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) = linkWeight m τ (η ∪ η') := by
    intro η' _
    simp only [linkWeight]
    congr 1
    ext x; simp only [mem_union]; tauto
  have e' : ∑ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) * f (τ ∪ η') * g (τ ∪ η) =
      ∑ η' ∈ W (link X τ) η, linkWeight m τ (η ∪ η') * loc f τ η' * loc g τ η :=
    sum_congr rfl (fun η' h => by simp only [e η' h, loc])
  rw [e']
  simp only [nonLazyWalk, upperWalk, if_pos hηL, hc, W, div_mul_eq_mul_div, ← Finset.sum_div,
    ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

lemma weighted_dStar {X : Finset (Finset V)} {m : Finset V → ℝ}
    {τ : Finset V} (hτ : τ ∈ X) (hm : m τ ≠ 0) (φ : Finset V → ℝ) :
    (∑ σ ∈ U X τ, m σ * φ σ) = m τ * dStar X m φ τ := by
  rw [dStar, if_pos hτ, mul_sum]
  apply sum_congr
  · ext σ
    simp only [U, mem_filter, and_comm, and_left_comm]
  · intro σ _
    field_simp

lemma link_summand_formula {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {m : Finset V → ℝ} (hm : IsWeight X n m)
    {k : ℕ} (hk : k + 1 ≤ n) {τ : Finset V} (hτ : τ ∈ cells X k)
    (φ ψ : Finset V → ℝ) :
    linkSummand X m τ φ ψ =
      (∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * φ σ' * ψ σ) - m τ * dStar X m φ τ * dStar X m ψ τ := by
  have hτX := (mem_filter.mp hτ).1
  have hτc := (mem_filter.mp hτ).2
  have hn : ∀ σ ∈ U X τ, σ.card ≤ n := by
    intro σ hσ
    have := (mem_filter.mp hσ).2.1
    omega
  have he : linkSummand X m τ φ ψ =
      ip (link X τ) (linkWeight m τ) 1
        (nonLazyWalk (link X τ) (linkWeight m τ) (loc (fun σ => φ σ - dStar X m φ τ) τ))
        (loc ψ τ) := by
    unfold linkSummand ip
    apply sum_congr rfl
    intro η hη
    congr 2
    apply nonLazy_congr _ _ hη
    intro η' hη'
    simp only [loc, lower_link_constant hX.1 m hτX φ hη']
  rw [he, link_pairing hX.1 hm.1]
  calc
    _ = ∑ σ ∈ U X τ,
        ((∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * ψ σ) -
          dStar X m φ τ * (m σ * ψ σ)) := by
      apply sum_congr rfl
      intro σ hσ
      have hw := R1 hX.1 hm hσ (hn σ hσ)
      calc
        _ = (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * ψ σ) -
            dStar X m φ τ * ((∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')) * ψ σ) := by
          simp only [mul_sum, sum_mul, ← sum_sub_distrib]
          apply sum_congr rfl
          intro σ' _
          ring
        _ = _ := by rw [hw]
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, weighted_dStar hτX (hm.1 τ hτX).ne' ψ]
      ring

end WalksLinkDecomposition

theorem WalksLinkDecomposition.proposition_4_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    ip X m (k + 2) (dS X φ) (dS X ψ) =
      ip X m k (dStar X m φ) (dStar X m ψ) + ip X m (k + 1) φ ψ + linkTerm X m k φ ψ := by
  have ht : linkTerm X m k φ ψ =
      (∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ) -
        ip X m k (dStar X m φ) (dStar X m ψ) := by
    unfold linkTerm
    rw [sum_congr rfl (fun τ hτ => WalksLinkDecomposition.link_summand_formula hX hm hk hτ φ ψ),
      sum_sub_distrib, G2 hX.1 k]
    rfl
  rw [key1a hX hm hk φ ψ, ht]
  unfold ip
  ring


#print axioms WalksLinkDecomposition.proposition_4_2


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLinkDecomposition

namespace WalksNormalization

variable {V : Type*} [DecidableEq V]

lemma ip_scale_left (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (a : ℝ) (f g : Finset V → ℝ) :
    ip X m c (fun σ => a * f σ) g = a * ip X m c f g := by
  unfold ip
  rw [mul_sum]
  apply sum_congr rfl
  intro σ _
  ring

lemma ip_scale (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (a : ℝ) (f : Finset V → ℝ) :
    ip X m c (fun σ => a * f σ) (fun σ => a * f σ) = a ^ 2 * ip X m c f f := by
  unfold ip
  rw [mul_sum]
  apply sum_congr rfl
  intro σ _
  ring

lemma dS_scale (X : Finset (Finset V)) (a : ℝ) (f : Finset V → ℝ) :
    dS X (fun σ => a * f σ) = fun σ => a * dS X f σ := by
  funext σ
  by_cases hσ : σ ∈ X <;> simp [dS, hσ, mul_sum]

lemma adjoint_pair {X : Finset (Finset V)} {m : Finset V → ℝ}
    (hpos : ∀ τ ∈ X, 0 < m τ) (k : ℕ) (f g : Finset V → ℝ) :
    ip X m (k + 1) f (dS X g) = ip X m k (dStar X m f) g := by
  unfold ip
  rw [ADJ X m k f g]
  apply sum_congr rfl
  intro τ hτ
  rw [weighted_dStar (mem_filter.mp hτ).1 (hpos τ (mem_filter.mp hτ).1).ne' f]
  ring

lemma adjoint_mean {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {m : Finset V → ℝ}
    (hpos : ∀ τ ∈ X, 0 < m τ) (k : ℕ) (f : Finset V → ℝ) :
    ip X m k (dStar X m f) (fun _ => 1) = ((k : ℝ) + 1) * ip X m (k + 1) f (fun _ => 1) := by
  have he : ip X m k (dStar X m f) (fun _ => 1) =
      ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, m σ * f σ := by
    unfold ip
    apply sum_congr rfl
    intro τ hτ
    rw [weighted_dStar (mem_filter.mp hτ).1 (hpos τ (mem_filter.mp hτ).1).ne' f, mul_one]
  rw [he, sumU hdc k]
  simp only [ip, mul_one]

lemma norm_zero_degree_zero {X : Finset (Finset V)} {m : Finset V → ℝ}
    {f : Finset V → ℝ} (hf : ip X m 0 f (fun _ => 1) = 0) : ip X m 0 f f = 0 := by
  have he : ip X m 0 f f = f ∅ * ip X m 0 f (fun _ => 1) := by
    unfold ip
    rw [mul_sum]
    apply sum_congr rfl
    intro τ hτ
    have hτ0 : τ = ∅ := card_eq_zero.mp (mem_filter.mp hτ).2
    rw [hτ0]
    ring
  rw [he, hf, mul_zero]

lemma normalize_numbers {N A E : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcs : A ^ 2 ≤ N * E) : ∃ a : ℝ, a ^ 2 * E = A ∧ a ^ 2 * A ≤ N := by
  by_cases hE0 : E = 0
  · have hA0 : A = 0 := by rw [hE0, mul_zero] at hcs; nlinarith only [hcs, hA]
    exact ⟨0, by simp [hA0], by simpa using hN⟩
  · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
    refine ⟨Real.sqrt (A / E), ?_, ?_⟩
    · rw [Real.sq_sqrt (div_nonneg hA hE), div_mul_cancel₀ _ hE0]
    · rw [Real.sq_sqrt (div_nonneg hA hE), div_mul_eq_mul_div]
      apply (div_le_iff₀ hEp).mpr
      nlinarith only [hcs]

lemma normalized_adjoint {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {m : Finset V → ℝ} (hm : IsWeight X n m)
    (k : ℕ) (f : Finset V → ℝ) (hf : ip X m (k + 1) f (fun _ => 1) = 0) :
    ∃ g : Finset V → ℝ,
      ip X m k g (fun _ => 1) = 0 ∧
      ip X m k g g ≤ ip X m (k + 1) f f ∧
      ip X m (k + 1) (dS X g) (dS X g) = ip X m k (dStar X m f) (dStar X m f) := by
  have hcs := ip_cs hm.1 (k + 1) f (dS X (dStar X m f))
  rw [adjoint_pair hm.1] at hcs
  obtain ⟨a, ha, han⟩ := normalize_numbers
    (ip_nonneg hm.1 (k + 1) f) (ip_nonneg hm.1 k (dStar X m f))
    (ip_nonneg hm.1 (k + 1) (dS X (dStar X m f))) hcs
  refine ⟨fun σ => a * dStar X m f σ, ?_, ?_, ?_⟩
  · rw [ip_scale_left, adjoint_mean hX.1 hm.1, hf, mul_zero, mul_zero]
  · rw [ip_scale]
    exact han
  · rw [dS_scale, ip_scale]
    exact ha

lemma norm_remainder {X : Finset (Finset V)} {m : Finset V → ℝ}
    (hpos : ∀ τ ∈ X, 0 < m τ) (c : ℕ) (f : Finset V → ℝ)
    (hf : ip X m c f (fun _ => 1) = 0) {B : ℝ} (hB : 0 ≤ B) (hBN : B ≤ ip X m c f f) :
    ∃ g : Finset V → ℝ,
      ip X m c g (fun _ => 1) = 0 ∧ ip X m c g g = ip X m c f f - B := by
  let N := ip X m c f f
  have hN : 0 ≤ N := ip_nonneg hpos c f
  by_cases hN0 : N = 0
  · have hB0 : B = 0 := by change B ≤ N at hBN; linarith
    refine ⟨fun _ => 0, by simp [ip], ?_⟩
    change ip X m c (fun _ => 0) (fun _ => 0) = N - B
    rw [hN0, hB0]
    simp [ip]
  · have hR : 0 ≤ (N - B) / N := div_nonneg (sub_nonneg.mpr hBN) hN
    refine ⟨fun σ => Real.sqrt ((N - B) / N) * f σ, ?_, ?_⟩
    · rw [ip_scale_left, hf, mul_zero]
    · rw [ip_scale, Real.sq_sqrt hR]
      exact div_mul_cancel₀ (N - B) hN0

end WalksNormalization


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLinkDecomposition WalksNormalization

theorem WalksDecomposition.theorem_5_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0) :
    ∃ phi phi' : ℕ → Finset V → ℝ,
      phi' k = φ ∧
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      (∀ j < k, ip X m (j + 1) (phi' j) (fun _ => 1) = 0) ∧
      (∀ j ≤ k, ip X m (j + 1) (phi' j) (phi' j) =
        ∑ i ∈ Finset.range (j + 1), ip X m (i + 1) (phi i) (phi i)) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) =
        ∑ j ∈ Finset.range (k + 1), ((k : ℝ) + 1 - j) * ip X m (j + 1) (phi j) (phi j) +
          ∑ j ∈ Finset.range (k + 1), linkTerm X m j (phi' j) (phi' j) := by
  induction k generalizing φ with
  | zero =>
    refine ⟨fun _ => φ, fun _ => φ, rfl, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact hφ
    · intro j hj
      omega
    · intro j hj
      have : j = 0 := by omega
      subst j
      simp
    · have hz : ip X m 0 (dStar X m φ) (dStar X m φ) = 0 :=
        norm_zero_degree_zero (by rw [adjoint_mean hX.1 hm.1, hφ, mul_zero])
      have he := WalksLinkDecomposition.proposition_4_2 X n hX m hm 0 hk φ φ
      simpa [hz] using he
  | succ k ih =>
    obtain ⟨g, hg0, hgn, hge⟩ := normalized_adjoint hX hm (k + 1) φ hφ
    obtain ⟨r, hr0, hrn⟩ := norm_remainder hm.1 (k + 1 + 1) φ hφ
      (ip_nonneg hm.1 (k + 1) g) hgn
    obtain ⟨p, q, hq, hp0, hq0, hnorm, he⟩ := ih (by omega) g hg0
    let p2 : ℕ → Finset V → ℝ := fun j => if j = k + 1 then r else p j
    let q2 : ℕ → Finset V → ℝ := fun j => if j = k + 1 then φ else q j
    have hp2 (j : ℕ) (hj : j ≤ k) : p2 j = p j := by simp [p2, show j ≠ k + 1 by omega]
    have hq2 (j : ℕ) (hj : j ≤ k) : q2 j = q j := by simp [q2, show j ≠ k + 1 by omega]
    have hp2top : p2 (k + 1) = r := by simp [p2]
    have hq2top : q2 (k + 1) = φ := by simp [q2]
    have hng : ip X m (k + 1) g g =
        ∑ i ∈ range (k + 1), ip X m (i + 1) (p i) (p i) := by
      simpa only [hq] using hnorm k (le_refl k)
    have hpSum : (∑ i ∈ range (k + 1), ip X m (i + 1) (p2 i) (p2 i)) =
        ∑ i ∈ range (k + 1), ip X m (i + 1) (p i) (p i) := by
      apply sum_congr rfl
      intro i hi
      rw [hp2 i (by have := mem_range.mp hi; omega)]
    refine ⟨p2, q2, hq2top, ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjtop : j = k + 1
      · subst j
        rw [hp2top]
        exact hr0
      · rw [hp2 j (by omega)]
        exact hp0 j (by omega)
    · intro j hj
      rw [hq2 j (by omega)]
      by_cases hjk : j = k
      · subst j
        rw [hq]
        exact hg0
      · exact hq0 j (by omega)
    · intro j hj
      by_cases hjtop : j = k + 1
      · subst j
        rw [hq2top, sum_range_succ, hp2top, hpSum, ← hng, hrn]
        ring
      · rw [hq2 j (by omega), hnorm j (by omega)]
        apply sum_congr rfl
        intro i hi
        rw [hp2 i (by have := mem_range.mp hi; omega)]
    · have hmain : (∑ j ∈ range (k + 1 + 1), (((k + 1 : ℕ) : ℝ) + 1 - j) *
            ip X m (j + 1) (p2 j) (p2 j)) =
          (∑ j ∈ range (k + 1), ((k : ℝ) + 1 - j) * ip X m (j + 1) (p j) (p j)) +
            ip X m (k + 1 + 1) φ φ := by
        rw [sum_range_succ, hp2top]
        have hs : (∑ j ∈ range (k + 1), (((k + 1 : ℕ) : ℝ) + 1 - j) *
              ip X m (j + 1) (p2 j) (p2 j)) =
            (∑ j ∈ range (k + 1), ((k : ℝ) + 1 - j) * ip X m (j + 1) (p j) (p j)) +
              ip X m (k + 1) g g := by
          rw [hng, ← sum_add_distrib]
          apply sum_congr rfl
          intro j hj
          rw [hp2 j (by have := mem_range.mp hj; omega)]
          push_cast
          ring
        rw [hs, hrn]
        push_cast
        ring
      have hlinks : (∑ j ∈ range (k + 1 + 1), linkTerm X m j (q2 j) (q2 j)) =
          (∑ j ∈ range (k + 1), linkTerm X m j (q j) (q j)) + linkTerm X m (k + 1) φ φ := by
        rw [sum_range_succ, hq2top]
        congr 1
        apply sum_congr rfl
        intro j hj
        rw [hq2 j (by have := mem_range.mp hj; omega)]
      rw [hmain, hlinks]
      have hE := WalksLinkDecomposition.proposition_4_2 X n hX m hm (k + 1) hk φ φ
      rw [← hge, he] at hE
      linarith only [hE]


#print axioms WalksDecomposition.theorem_5_2


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLinkDecomposition

namespace WalksLinkBound

variable {V : Type*} [DecidableEq V]

lemma link_bound {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {m : Finset V → ℝ} (hm : IsWeight X n m)
    {k : ℕ} (hk : k + 1 ≤ n) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : LinkUpper X m k μ)
    {τ : Finset V} (hτ : τ ∈ cells X k) (φ : Finset V → ℝ) :
    linkSummand X m τ φ φ ≤ μ * ∑ σ ∈ U X τ, m σ * φ σ * φ σ := by
  have hτX := (mem_filter.mp hτ).1
  have hmτ := hm.1 τ hτX
  have hle := local_ineq hX hm hk hμ hτ φ
  have hA : (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ =
      m τ * dStar X m φ τ * dStar X m φ τ := by
    rw [weighted_dStar hτX hmτ.ne' φ]
    field_simp
  rw [hA] at hle
  rw [link_summand_formula hX hm hk hτ φ φ]
  have hp : 0 ≤ μ * (m τ * dStar X m φ τ * dStar X m φ τ) := by
    have hsq := mul_nonneg hmτ.le (sq_nonneg (dStar X m φ τ))
    apply mul_nonneg hμ0
    nlinarith only [hsq]
  nlinarith only [hle, hp]

end WalksLinkBound

theorem WalksLinkBound.lemma_4_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : LinkUpper X m k μ)
    (φ : Finset V → ℝ) :
    linkTerm X m k φ φ ≤ ((k : ℝ) + 1) * μ * ip X m (k + 1) φ φ := by
  unfold linkTerm
  calc
    _ ≤ ∑ τ ∈ cells X k, μ * ∑ σ ∈ U X τ, m σ * φ σ * φ σ :=
      sum_le_sum (fun τ hτ => WalksLinkBound.link_bound hX hm hk hμ0 hμ hτ φ)
    _ = _ := by
      rw [← mul_sum, sumU hX.1 k]
      unfold ip
      ring



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided Finset

namespace WalksCorollary

lemma triangle_sum (k : ℕ) (a b : ℕ → ℝ) :
    (∑ j ∈ range (k + 1), a j * ∑ i ∈ range (j + 1), b i) =
      ∑ i ∈ range (k + 1), (∑ j ∈ Icc i k, a j) * b i := by
  simp_rw [mul_sum]
  rw [Finset.sum_comm' (t' := range (k + 1)) (s' := fun i => Icc i k)]
  · apply sum_congr rfl
    intro i _
    rw [sum_mul]
  · intro j i
    simp only [mem_range, mem_Icc]
    omega

end WalksCorollary


/-- Corollary 5.3, pp. 16–17, with the correction `0 ≤ μ_i`: every link of dimension at least one
is connected, and for `0 ≤ k ≤ n - 1`, if `μ_i ≥ 0`
bounds the second largest eigenvalue of `(M')⁺_{τ,0}` for every `τ ∈ X(i-1)`, `0 ≤ i ≤ k`, then
every `φ ∈ C^k_0(X, ℝ)` has `φ^j ∈ C^j_0(X, ℝ)` with `‖φ‖² = ‖φ^k‖² + … + ‖φ^0‖²` and
`‖dφ‖² ≤ Σ_{j=0}^k (k + 1 - j + Σ_{i=j}^k (i+1) μ_i) ‖φ^j‖²`. -/
theorem WalksCorollary.corollary_5_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (hconn : ∀ c : ℕ, c + 1 ≤ n → ∀ τ ∈ cells X c,
      ∀ u ∈ cells (link X τ) 1, ∀ v ∈ cells (link X τ) 1,
        Relation.ReflTransGen
          (fun a b : Finset V => a ∈ cells (link X τ) 1 ∧ b ∈ cells (link X τ) 1 ∧
            a ∪ b ∈ cells (link X τ) 2) u v)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0)
    (μ : ℕ → ℝ) (hμ : ∀ i ≤ k, 0 ≤ μ i ∧ LinkUpper X m i (μ i)) :
    ∃ phi : ℕ → Finset V → ℝ,
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      ip X m (k + 1) φ φ = ∑ j ∈ Finset.range (k + 1), ip X m (j + 1) (phi j) (phi j) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) ≤
        ∑ j ∈ Finset.range (k + 1),
          ((k : ℝ) + 1 - j + ∑ i ∈ Finset.Icc j k, ((i : ℝ) + 1) * μ i) *
            ip X m (j + 1) (phi j) (phi j) := by
  obtain ⟨p, q, hq, hp0, hq0, hnorm, he⟩ :=
    WalksDecomposition.theorem_5_2 X n hX m hm k hk φ hφ
  refine ⟨p, hp0, ?_, ?_⟩
  · simpa only [hq] using hnorm k (le_refl k)
  · have hb : (∑ j ∈ range (k + 1), linkTerm X m j (q j) (q j)) ≤
        ∑ j ∈ range (k + 1), (((j : ℝ) + 1) * μ j) *
          ∑ i ∈ range (j + 1), ip X m (i + 1) (p i) (p i) := by
      apply sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := mem_range.mp hj; omega
      rw [← hnorm j hjk]
      exact WalksLinkBound.lemma_4_3 X n hX m hm j (by omega) (μ j) (hμ j hjk).1 (hμ j hjk).2 (q j)
    rw [he]
    calc
      _ ≤ (∑ j ∈ range (k + 1), ((k : ℝ) + 1 - j) * ip X m (j + 1) (p j) (p j)) +
          ∑ j ∈ range (k + 1), (((j : ℝ) + 1) * μ j) *
            ∑ i ∈ range (j + 1), ip X m (i + 1) (p i) (p i) := add_le_add le_rfl hb
      _ = _ := by
        rw [WalksCorollary.triangle_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        ring




#print axioms WalksCorollary.corollary_5_3


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided Finset

namespace WalksCorollaryUniform

lemma interval_sum (i k : ℕ) (hik : i ≤ k) (a : ℝ) :
    (∑ j ∈ Icc i k, ((j : ℝ) + 1) * a) =
      ((k : ℝ) + i + 2) * ((k : ℝ) + 1 - i) / 2 * a := by
  induction k, hik using Nat.le_induction with
  | base => rw [Icc_self, sum_singleton]; ring
  | succ k hik ih =>
    rw [sum_Icc_succ_top (by omega : i ≤ k + 1), ih]
    push_cast
    ring

end WalksCorollaryUniform


/-- Corollary 5.3 ("In particular"), p. 17, with the correction `0 ≤ λ`: if every link of
dimension at least one is connected and `X` is a one-sided `λ`-local spectral expander, then
every `φ ∈ C^k_0(X, ℝ)` (`0 ≤ k ≤ n - 1`) has
`φ^j ∈ C^j_0(X, ℝ)` with `‖φ‖² = ‖φ^k‖² + … + ‖φ^0‖²` and
`‖dφ‖² ≤ Σ_{j=0}^k (k + 1 - j + ((k+j+2)(k+1-j)/2) λ) ‖φ^j‖²`. -/
theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (hconn : ∀ c : ℕ, c + 1 ≤ n → ∀ τ ∈ cells X c,
      ∀ u ∈ cells (link X τ) 1, ∀ v ∈ cells (link X τ) 1,
        Relation.ReflTransGen
          (fun a b : Finset V => a ∈ cells (link X τ) 1 ∧ b ∈ cells (link X τ) 1 ∧
            a ∪ b ∈ cells (link X τ) 2) u v)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (hexp : OneSidedLSE X m n lam) :
    ∃ phi : ℕ → Finset V → ℝ,
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      ip X m (k + 1) φ φ = ∑ j ∈ Finset.range (k + 1), ip X m (j + 1) (phi j) (phi j) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) ≤
        ∑ j ∈ Finset.range (k + 1),
          ((k : ℝ) + 1 - j + ((k : ℝ) + j + 2) * ((k : ℝ) + 1 - j) / 2 * lam) *
            ip X m (j + 1) (phi j) (phi j) := by
  obtain ⟨p, hp0, hpn, hpe⟩ := WalksCorollary.corollary_5_3 X n hX m hm hconn k hk φ hφ
    (fun _ => lam) (fun i hi => ⟨hlam, hexp i (by omega)⟩)
  refine ⟨p, hp0, hpn, ?_⟩
  convert hpe using 1
  apply sum_congr rfl
  intro j hj
  rw [WalksCorollaryUniform.interval_sum j k (by have := mem_range.mp hj; omega)]



#print axioms solution
