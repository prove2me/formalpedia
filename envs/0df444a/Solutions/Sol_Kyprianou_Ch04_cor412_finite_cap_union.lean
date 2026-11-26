-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_finite_cap_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:23.221876+00:00
-- url     : https://prove2.me/submissions/e8260628-d52e-49cf-8d71-45f9ded457e4

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The increasing finite integer caps exhaust the finite extended-clock event. -/
theorem solution
    {Ω : Type} (τ : Ω → WithTop NNReal) :
    (⋃ n : ℕ, {w : Ω | τ w ≤ ((n : NNReal) : WithTop NNReal)}) =
      {w : Ω | τ w ≠ ⊤} := by
  ext w
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n,hn⟩
    exact ne_of_lt (hn.trans_lt (WithTop.coe_lt_top _))
  · intro hw
    cases ht : τ w with
    | top => exact (hw ht).elim
    | coe t =>
      obtain ⟨n,hn⟩ := exists_nat_ge t
      exact ⟨n, WithTop.coe_le_coe.mpr hn⟩
