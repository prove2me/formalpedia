-- Prove2me | solution 1 for N25.LocalFive.finite_algHom_of_finite_target
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:18.613976+00:00
-- url     : https://prove2.me/submissions/f3128105-d4e8-421e-957d-748a26ab3c8f

import Mathlib

noncomputable section

namespace N25.LocalFive

/-- Finite-type algebras have finitely many maps into a finite target ring. -/
theorem _root_.solution
    {R A T : Type*}
    [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T]
    [Algebra.FiniteType R A] [Finite T] :
    Finite (A →ₐ[R] T) := by
  classical
  let s := Algebra.EssFiniteType.finset R A
  let restrict : (A →ₐ[R] T) → (s → T) := fun f a => f a
  apply Finite.of_injective restrict
  intro f g h
  apply Algebra.EssFiniteType.algHom_ext
  intro a ha
  exact congrFun h ⟨a, ha⟩

end N25.LocalFive
