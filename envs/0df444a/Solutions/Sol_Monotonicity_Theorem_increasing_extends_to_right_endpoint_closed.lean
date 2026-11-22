-- Prove2me | solution 1 for Monotonicity_Theorem.increasing_extends_to_right_endpoint_closed
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-12T13:26:53.549858+00:00
-- url     : https://prove2.me/submissions/f5eeb448-87c4-415f-91ea-14351ce76739

import Definitions.Def_Monotonicity_Theorem_Framework

theorem solution {R : Type}
    (D : Monotonicity_Theorem.DenseLinearOrderNoEndpoints R)
    {I B : Set (Monotonicity_Theorem.Power R 1)}
    (f : {x : Monotonicity_Theorem.Power R 1 // I x} → {y : Monotonicity_Theorem.Power R 1 // B y})
    (x₀ s : R) (hxs : D.lt x₀ s)
    (hI : ∀ x : Monotonicity_Theorem.Power R 1, I x → Monotonicity_Theorem.Power.coord1 x = x₀ ∨
      (D.lt x₀ (Monotonicity_Theorem.Power.coord1 x) ∧ D.lt (Monotonicity_Theorem.Power.coord1 x) s) ∨ Monotonicity_Theorem.Power.coord1 x = s)
    (hleft : ∀ x y (hx : I x) (hy : I y),
      D.lt (Monotonicity_Theorem.Power.coord1 x) s → D.lt (Monotonicity_Theorem.Power.coord1 y) s →
      Monotonicity_Theorem.Lt1 D x y → Monotonicity_Theorem.Lt1 D (f ⟨x, hx⟩).1 (f ⟨y, hy⟩).1)
    (hbound : ∀ u (hu : I u) y (hy : I y),
      (Monotonicity_Theorem.Power.coord1 u = x₀ ∨ D.lt x₀ (Monotonicity_Theorem.Power.coord1 u)) →
      D.lt (Monotonicity_Theorem.Power.coord1 u) s → Monotonicity_Theorem.Power.coord1 y = s →
      Monotonicity_Theorem.Lt1 D (f ⟨u, hu⟩).1 (f ⟨y, hy⟩).1) :
    Monotonicity_Theorem.StrictlyIncreasingOn D I B f := by
  unfold Monotonicity_Theorem.StrictlyIncreasingOn Monotonicity_Theorem.Lt1
  intro x y hx hy hlt
  rcases hI x hx with hx0 | ⟨⟨hxm1, hxm2⟩ | hxsx⟩
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hx0, hy0] at hlt
      exact D.irrefl x₀ hlt
    · exact hleft x y hx hy (by rw [hx0]; exact hxs) hym2 hlt
    · exact hbound x hx y hy (Or.inl hx0) (by rw [hx0]; exact hxs) hysy
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hy0] at hlt
      exact D.irrefl x₀ (D.trans hxm1 hlt)
    · exact hleft x y hx hy hxm2 hym2 hlt
    · exact hbound x hx y hy (Or.inr hxm1) hxm2 hysy
  · rcases hI y hy with hy0 | ⟨⟨hym1, hym2⟩ | hysy⟩
    · exfalso
      rw [hxsx, hy0] at hlt
      exact D.irrefl s (D.trans hlt hxs)
    · exfalso
      rw [hxsx] at hlt
      exact D.irrefl s (D.trans hlt hym2)
    · exfalso
      rw [hxsx, hysy] at hlt
      exact D.irrefl s hlt
