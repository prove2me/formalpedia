-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_monomials_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:50:16.240124+00:00
-- url     : https://prove2.me/submissions/ac2521cc-5b9f-42f9-a79e-e4bc06861667

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (n : Fin d → Nat) :
    ({f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
      (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)}).Finite := by
  classical
  let B : Set (Fin d → Nat) := Set.univ.pi (fun i => Set.Iio (n i))
  have hB : B.Finite := by
    dsimp [B]
    exact Set.Finite.pi (fun i => Set.finite_Iio (n i))
  let E := Finsupp.equivFunOnFinite (α := Fin d) (M := Nat)
  let A : Set (Fin d →₀ Nat) := {a | ∀ i, a i < n i}
  have hA : A = Set.image E.symm B := by
    ext a
    simp only [A, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro ha
      refine ⟨E a, ?_, ?_⟩
      · have hcoords : ∀ i, (E a) i < n i := by
          simpa [E] using ha
        simpa [B, Set.mem_pi] using hcoords
      · simp
    · rintro ⟨x, hx, rfl⟩
      have hx' : ∀ i, x i < n i := by
        simpa [B, Set.mem_pi] using hx
      change ∀ i, (E.symm x) i < n i
      simpa [E] using hx'
  have hAfinite : A.Finite := by
    rw [hA]
    exact hB.image E.symm
  let T : Set (MvPolynomial (Fin d) ℂ) :=
    {f | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
      f = MvPolynomial.monomial a (1 : ℂ)}
  have hT : T = Set.image
      (fun a : Fin d →₀ Nat => MvPolynomial.monomial a (1 : ℂ)) A := by
    ext f
    simp only [T, A, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hf⟩
      exact ⟨a, ha, hf.symm⟩
    · rintro ⟨a, ha, hf⟩
      exact ⟨a, ha, hf.symm⟩
  change T.Finite
  rw [hT]
  exact hAfinite.image _
