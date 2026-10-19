-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.right_derivative_preserves_secant_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:01:06.197206+00:00
-- url     : https://prove2.me/submissions/26940ce1-c6a4-4819-b9dc-e6a99186f9e6

import Mathlib
set_option autoImplicit false

open Filter
open scoped Topology

theorem solution
    (g : ℝ → ℝ) (a r c : ℝ)
    (hderiv : HasDerivWithinAt g r (Set.Ici a) a)
    (hsec : ∀ y, a < y → c ≤ slope g a y) :
    c ≤ r := by
  have h := (hasDerivWithinAt_iff_tendsto_slope.mp hderiv)
  have e : Set.Ici a \ {a} = Set.Ioi a := by
    ext y
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h1; exact ⟨h1.le, h1.ne'⟩
  rw [e] at h
  exact ge_of_tendsto h (eventually_nhdsWithin_of_forall fun y hy => hsec y hy)
