-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Descent.thicken_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:55:19.521595+00:00
-- url     : https://prove2.me/submissions/1147bc5d-3823-4e67-be22-2fa3a0617b48

import Mathlib

open Set

theorem solution {X : Type*} [TopologicalSpace X] [CompactSpace X] {f g : X → ℝ} {ℓ : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hℓ : Continuous ℓ)
    (c a : ℝ) (h : ∀ x, f x ≤ c → ℓ x = 0 → g x < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x ≤ c + ε → ℓ x = 0 → g x < a := by
  by_contra hcon
  push Not at hcon
  let t : ℕ → Set X := fun i => {x | f x ≤ c + 1 / ((i : ℝ) + 1)} ∩ {x | ℓ x = 0} ∩ {x | a ≤ g x}
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i x hx
    refine ⟨⟨show f x ≤ c + 1 / ((i : ℝ) + 1) from le_trans hx.1.1 ?_, hx.1.2⟩, hx.2⟩
    have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have : 1 / ((((i + 1 : ℕ) : ℝ)) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le this; push_cast; linarith
    exact add_le_add_right this c
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨x, h1, h2, h3⟩ := hcon (1 / ((i : ℝ) + 1)) (by positivity)
    exact ⟨x, ⟨h1, h2⟩, h3⟩
  have htcl : ∀ i, IsClosed (t i) := fun i =>
    ((isClosed_le hf continuous_const).inter (isClosed_eq hℓ continuous_const)).inter
      (isClosed_le continuous_const hg)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (htcl 0).isCompact htcl
  rw [mem_iInter] at hx
  have hfx : f x ≤ c := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have : f x ≤ c + 1 / ((n : ℝ) + 1) := (hx n).1.1
    linarith
  exact absurd (h x hfx (hx 0).1.2) (not_lt.2 (hx 0).2)
