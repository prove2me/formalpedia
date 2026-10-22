-- Prove2me | solution 1 for HighOrderWalks.TwoSided.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:07:37.690388+00:00
-- url     : https://prove2.me/submissions/14e72417-ed87-4a55-92dc-530627c1b4ff

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

set_option autoImplicit false
open HighOrderWalks.OneSided

theorem swap_lemma {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m) (c : ℕ)
    (φ ψ : Finset V → ℝ) :
    HighOrderWalks.OneSided.ip X m (c + 1) (HighOrderWalks.OneSided.dS X φ) ψ =
      HighOrderWalks.OneSided.ip X m c φ (HighOrderWalks.OneSided.dStar X m ψ) := by
  unfold ip
  have hL : ∀ σ ∈ cells X (c + 1), m σ * dS X φ σ * ψ σ =
      ∑ τ ∈ X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card), m σ * φ τ * ψ σ := by
    intro σ hσ
    have hσX : σ ∈ X := (Finset.mem_filter.mp hσ).1
    simp only [dS, if_pos hσX, Finset.mul_sum, Finset.sum_mul]
  have hR : ∀ τ ∈ cells X c, m τ * φ τ * dStar X m ψ τ =
      ∑ σ ∈ X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1), m σ * φ τ * ψ σ := by
    intro τ hτ
    have hτX : τ ∈ X := (Finset.mem_filter.mp hτ).1
    have hpos : m τ ≠ 0 := (hm.1 τ hτX).ne'
    simp only [dStar, if_pos hτX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    field_simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  apply Finset.sum_comm'
  intro σ τ
  simp only [cells, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, c1, d, e⟩
    exact ⟨⟨a, d, by omega⟩, c1, by omega⟩
  · rintro ⟨⟨a, d, e⟩, c1, f⟩
    exact ⟨⟨a, by omega⟩, c1, d, by omega⟩

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (∀ φ : Finset V → ℝ, (∀ τ ∈ HighOrderWalks.OneSided.cells X k, HighOrderWalks.OneSided.dStar X m φ τ = 0) →
        HighOrderWalks.OneSided.ip X m (k + 1) φ (fun _ => 1) = 0) ∧
      ∀ ψ : Finset V → ℝ,
        HighOrderWalks.OneSided.ip X m k ψ (fun _ => 1) = 0 ↔ HighOrderWalks.OneSided.ip X m (k + 1) (HighOrderWalks.OneSided.dS X ψ) (fun _ => 1) = 0 := by
  constructor
  · intro φ hφ
    have h1 := swap_lemma X n m hm k (fun _ => 1) φ
    have hL : ip X m (k + 1) (dS X (fun _ => 1)) φ = ((k : ℝ) + 1) * ip X m (k + 1) φ (fun _ => 1) := by
      unfold ip
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      have hσX : σ ∈ X := (Finset.mem_filter.mp hσ).1
      have hσc : σ.card = k + 1 := (Finset.mem_filter.mp hσ).2
      have hcard : (X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card)).card = k + 1 := by
        have : X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card) = Finset.powersetCard k σ := by
          ext τ
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          constructor
          · rintro ⟨_, h1, h2⟩
            exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩
            exact ⟨hX.1 σ hσX τ h1, h1, by omega⟩
        rw [this, Finset.card_powersetCard, hσc, Nat.choose_succ_self_right]
      simp only [dS, if_pos hσX, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
      push_cast
      ring
    have hR : ip X m k (fun _ => 1) (dStar X m φ) = 0 := by
      unfold ip
      refine Finset.sum_eq_zero fun τ hτ => ?_
      rw [hφ τ hτ]
      ring
    rw [hL, hR] at h1
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1).resolve_left hk1
  · intro ψ
    have h1 := swap_lemma X n m hm k ψ (fun _ => 1)
    have hR : ip X m k ψ (dStar X m (fun _ => 1)) = ip X m k ψ (fun _ => 1) := by
      unfold ip
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hτX : τ ∈ X := (Finset.mem_filter.mp hτ).1
      have hτc : τ.card = k := (Finset.mem_filter.mp hτ).2
      have hpos : m τ ≠ 0 := (hm.1 τ hτX).ne'
      have hw := hm.2 τ hτX (by omega)
      have hsum : ∑ σ ∈ X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1), m σ / m τ * 1 = 1 := by
        have e : X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1) =
            X.filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ) := by
          ext σ; simp only [Finset.mem_filter]; tauto
        rw [e]
        simp only [mul_one]
        rw [← Finset.sum_div, ← hw]
        exact div_self hpos
      simp only [dStar, if_pos hτX]
      rw [hsum]
    rw [hR] at h1
    rw [← h1]
