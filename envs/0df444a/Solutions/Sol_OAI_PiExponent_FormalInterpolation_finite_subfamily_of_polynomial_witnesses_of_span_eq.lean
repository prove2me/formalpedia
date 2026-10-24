-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_subfamily_of_polynomial_witnesses_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:28:13.742731+00:00
-- url     : https://prove2.me/submissions/555b764c-758a-44ab-8e5a-23d538806e31

import Mathlib

theorem solution
    {d : Nat} {α : Type}
    (F : α → MvPolynomial (Fin d) Complex)
    (m : Nat) (idx : Fin m → α)
    (hspan :
      Ideal.span (Set.range (fun j : Fin m => F (idx j))) =
        Ideal.span (Set.range F))
    (h : ∀ x : Fin d → Complex,
      (∀ a : α, MvPolynomial.eval x (F a) = 0) →
      ∀ i : Fin d, x i = 0) :
    ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (F (idx j)) = 0) →
      ∀ i : Fin d, x i = 0 := by
  intro x hx
  apply h x
  intro a
  have hmem : F a ∈ Ideal.span (Set.range (fun j : Fin m => F (idx j))) := by
    rw [hspan]; exact Ideal.subset_span ⟨a, rfl⟩
  have hle : Ideal.span (Set.range (fun j : Fin m => F (idx j))) ≤ RingHom.ker (MvPolynomial.eval x) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hx j
  exact hle hmem
