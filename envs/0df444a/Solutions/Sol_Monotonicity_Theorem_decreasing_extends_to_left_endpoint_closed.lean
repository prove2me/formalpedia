-- Prove2me | solution 1 for Monotonicity_Theorem.decreasing_extends_to_left_endpoint_closed
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-12T13:47:41.866984+00:00
-- url     : https://prove2.me/submissions/737bc2b2-898c-4e3a-82e2-c9fda77bfff0

import Definitions.Def_Monotonicity_Theorem_Framework

theorem solution {R : Type}
    (D : Monotonicity_Theorem.DenseLinearOrderNoEndpoints R)
    {I B : Set (Monotonicity_Theorem.Power R 1)}
    (f : {x : Monotonicity_Theorem.Power R 1 // I x} → {y : Monotonicity_Theorem.Power R 1 // B y})
    (s x₀ : R) (hxs : D.lt s x₀)
    (hI : ∀ x : Monotonicity_Theorem.Power R 1, I x → Monotonicity_Theorem.Power.coord1 x = s ∨
      (D.lt s (Monotonicity_Theorem.Power.coord1 x) ∧ D.lt (Monotonicity_Theorem.Power.coord1 x) x₀) ∨ Monotonicity_Theorem.Power.coord1 x = x₀)
    (hleft : ∀ x y (hx : I x) (hy : I y),
      D.lt s (Monotonicity_Theorem.Power.coord1 x) → D.lt s (Monotonicity_Theorem.Power.coord1 y) →
      Monotonicity_Theorem.Lt1 D x y → Monotonicity_Theorem.Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1)
    (hbound : ∀ u (hu : I u) y (hy : I y),
      (D.lt (Monotonicity_Theorem.Power.coord1 u) x₀ ∨ Monotonicity_Theorem.Power.coord1 u = x₀) →
      D.lt s (Monotonicity_Theorem.Power.coord1 u) → Monotonicity_Theorem.Power.coord1 y = s →
      Monotonicity_Theorem.Lt1 D (f ⟨u, hu⟩).1 (f ⟨y, hy⟩).1) :
    Monotonicity_Theorem.StrictlyDecreasingOn D I B f := by
  unfold Monotonicity_Theorem.StrictlyDecreasingOn Monotonicity_Theorem.Lt1
  intro x y hx hy hlt
  rcases hI x hx with hx0 | ⟨⟨hxm1, hxm2⟩ | hxsx⟩
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hx0, hy0] at hlt
      exact D.irrefl s hlt
    · exact hbound y hy x hx (Or.inl hym2) hym1 hx0
    · exact hbound y hy x hx (Or.inr hysy) (by rw [hysy]; exact hxs) hx0
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hy0] at hlt
      exact D.irrefl s (D.trans hxm1 hlt)
    · exact hleft x y hx hy hxm1 hym1 hlt
    · exact hleft x y hx hy hxm1 (by rw [hysy]; exact hxs) hlt
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hxsx, hy0] at hlt
      exact D.irrefl x₀ (D.trans hlt hxs)
    · exfalso
      rw [hxsx] at hlt
      exact D.irrefl x₀ (D.trans hlt hym2)
    · exfalso
      rw [hxsx, hysy] at hlt
      exact D.irrefl x₀ hlt
