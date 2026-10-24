-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_by_coordinate_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:32:53.256175+00:00
-- url     : https://prove2.me/submissions/ba779c7b-e2ab-43aa-8d18-50873bcbc2ca

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

universe u

theorem solution
    {R : Type u} [CommRing R] {d : Nat}
    (e : Fin d → Nat) (he : ∀ i : Fin d, 0 < e i) :
    Module.Finite R ((MvPolynomial (Fin d) R) ⧸
      Ideal.span (Set.range fun i : Fin d =>
        (MvPolynomial.X i : MvPolynomial (Fin d) R) ^ e i)) := by
  classical
  let I : Ideal (MvPolynomial (Fin d) R) :=
    Ideal.span (Set.range fun i : Fin d =>
      (MvPolynomial.X i : MvPolynomial (Fin d) R) ^ e i)
  let q : MvPolynomial (Fin d) R →ₐ[R] (MvPolynomial (Fin d) R) ⧸ I :=
    Ideal.Quotient.mkₐ R I
  let s : Set ((MvPolynomial (Fin d) R) ⧸ I) :=
    Set.range fun i : Fin d => q (MvPolynomial.X i)
  have hs : s.Finite := Set.finite_range _
  have hpow (i : Fin d) : (q (MvPolynomial.X i)) ^ e i = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_range.mpr ⟨i, rfl⟩)
  have hsi : ∀ x ∈ s, IsIntegral R x := by
    rintro x ⟨i, rfl⟩
    apply IsIntegral.of_pow (he i)
    rw [hpow]
    exact isIntegral_zero
  let S : Subalgebra R ((MvPolynomial (Fin d) R) ⧸ I) := Algebra.adjoin R s
  have hS : Module.Finite R S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hs hsi
  have htop : S = ⊤ := by
    dsimp [S, s]
    calc
      Algebra.adjoin R (Set.range fun i : Fin d => q (MvPolynomial.X i)) =
          Algebra.adjoin R (q '' Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)) := by
        congr 1
        ext y
        simp
      _ = (Algebra.adjoin R (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map q :=
        (AlgHom.map_adjoin q _).symm
      _ = ⊤ := by
        rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
        exact (AlgHom.range_eq_top q).2 (Ideal.Quotient.mkₐ_surjective R I)
  let f : S →ₗ[R] ((MvPolynomial (Fin d) R) ⧸ I) := S.toSubmodule.subtype
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ S := by rw [htop]; trivial
    exact ⟨⟨y, hy⟩, rfl⟩
  exact Module.Finite.of_surjective f hf