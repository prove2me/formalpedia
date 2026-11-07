-- Prove2me | solution 1 for HighOrderWalks.OneSided.corollary_3_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:49:53.225981+00:00
-- url     : https://prove2.me/submissions/4d01f2f8-46de-40f5-a32c-24fdce7a6a2b

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

/- Incidence and upper-energy helpers adapted from Nickrobbins95, accepted submission f3347acc-2e62-4054-8da8-fa7228623546. -/
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


end HOW54


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

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) :
    (∀ τ ∈ cells X (k + 1), dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ) ∧
      (∀ τ ∈ cells X (k + 1), dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ) := by
  exact ⟨WalksLaplacianIdentity.upper_identity X n hX m hm k hk φ,
    WalksLaplacianIdentity.lower_identity X m k φ⟩


#print axioms solution
