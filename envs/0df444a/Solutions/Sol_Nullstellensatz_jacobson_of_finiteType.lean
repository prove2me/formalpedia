-- Prove2me | solution 1 for Nullstellensatz.jacobson_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:41:45.940855+00:00
-- url     : https://prove2.me/submissions/fba470b5-0c94-4541-9f18-b4fa6f2085e6

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem aux_njft_finite {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsJacobsonRing R] [Algebra.FiniteType R A] (m : Ideal A) [m.IsMaximal] :
    Module.Finite R (A ⧸ m) := by
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType R (A ⧸ m) :=
    Algebra.FiniteType.trans (S := A) ‹_› inferInstance
  exact finite_of_finite_type_of_isJacobsonRing R (A ⧸ m)

theorem aux_njft_comap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (m : Ideal A) :
    Ideal.comap (algebraMap R (A ⧸ m)) ⊥ = m.comap (algebraMap R A) := by
  rw [IsScalarTower.algebraMap_eq R A (A ⧸ m), ← Ideal.comap_comap]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

end Nullstellensatz

open Nullstellensatz

theorem solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsJacobsonRing R] [Algebra.FiniteType R A] :
    IsJacobsonRing A ∧
      ∀ m : Ideal A, m.IsMaximal →
        (m.comap (algebraMap R A)).IsMaximal ∧
          Module.Finite (R ⧸ m.comap (algebraMap R A)) (A ⧸ m) := by
  refine ⟨isJacobsonRing_of_finiteType (A := R), fun m hm => ?_⟩
  have hfin : Module.Finite R (A ⧸ m) := aux_njft_finite m
  refine ⟨?_, Module.Finite.of_restrictScalars_finite R _ _⟩
  let := Ideal.Quotient.field m
  have : Algebra.IsIntegral R (A ⧸ m) := Algebra.IsIntegral.of_finite R (A ⧸ m)
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal (A ⧸ m))
  rwa [aux_njft_comap] at h
