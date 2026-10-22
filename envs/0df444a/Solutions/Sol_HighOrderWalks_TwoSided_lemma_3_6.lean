-- Prove2me | solution 1 for HighOrderWalks.TwoSided.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:06:17.686321+00:00
-- url     : https://prove2.me/submissions/22549b10-7c37-42c0-b064-fc2cae6d543c

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

set_option autoImplicit false
open HighOrderWalks.OneSided

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m) (c : ℕ) (hc : c ≤ n)
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
