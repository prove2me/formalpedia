-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.normal_basis_separation_logarithmic_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T08:47:36.377986+00:00
-- url     : https://prove2.me/submissions/86ff2c6a-9b35-42b2-b10e-c04f7b5d0046

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ordered_shear_has_relation_pivot
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_nonzero_proper_ideal_has_escaping_partial
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_prime_equations_derivation_relation
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution_prime_field_map_eq_zero_iff
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (F : MvPolynomial (Fin (m + 1)) Complex) :
    algebraMap (MvPolynomial (Fin (m + 1)) Complex)
      (logarithmicPrimeField P) F = 0 ↔ F ∈ P := by
  rw [IsScalarTower.algebraMap_apply
      (MvPolynomial (Fin (m + 1)) Complex)
      (MvPolynomial (Fin (m + 1)) Complex ⧸ P)
      (logarithmicPrimeField P),
    IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        coordinateNormalBasisAtPrime P A →
        logarithmicNormalBasisAtPrime P B →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ z : logarithmicPrimeField P,
      ∀ D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P),
        D z =
          D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1)))) /
          algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1))) := by
  classical
  let K := logarithmicPrimeField P
  let x : Fin (m + 1) → K := fun i =>
    algebraMap (MvPolynomial (Fin (m + 1)) Complex) K (MvPolynomial.X i)
  let y : K := x 0
  let u : Fin (m + 1) → P → K := coordinateNormalColumnAtPrime P
  let v : Fin (m + 1) → P → K := logarithmicNormalColumnAtPrime P
  have hy : y ≠ 0 := by
    intro h
    exact hY ((solution_prime_field_map_eq_zero_iff P (MvPolynomial.X 0)).mp h)
  have hnonzero : ∃ i, u i ≠ 0 := by
    obtain ⟨F, hF, i, hi⟩ :=
      nonzero_proper_ideal_has_escaping_partial P hP
        (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime))
    refine ⟨i, ?_⟩
    intro hcol
    apply hi
    apply (solution_prime_field_map_eq_zero_iff P (MvPolynomial.pderiv i F)).mp
    have he := congrFun hcol (⟨F, hF⟩ : P)
    change algebraMap (MvPolynomial (Fin (m + 1)) Complex) K
      (MvPolynomial.pderiv i F) = 0 at he
    exact he
  have hvzero : v 0 = y • u 0 + ∑ j : Fin m, u j.succ := by
    funext F
    simp [K, v, u, y, x, logarithmicNormalColumnAtPrime,
      coordinateNormalColumnAtPrime, logarithmicFrameDerivative,
      map_add, map_mul, map_sum, Finset.sum_apply, smul_eq_mul, Algebra.smul_def]
  have hvsucc : ∀ j : Fin m, v j.succ = u j.succ := by
    intro j
    funext F
    simp [v, u, logarithmicNormalColumnAtPrime,
      coordinateNormalColumnAtPrime, logarithmicFrameDerivative]
  obtain ⟨i, hpivot⟩ :=
    ordered_shear_has_relation_pivot u v y hy hvzero hvsucc hnonzero
      (by
        intro A B hcard hA hB
        exact hexclusion A B hcard hA hB)
  have hchain (D : Derivation Complex K K) :
      (∑ j : Fin (m + 1), D (x j) • u j) = 0 := by
    exact prime_equations_derivation_relation P D
  have hrelation (D : Derivation Complex K K) :
      (∑ j : Fin (m + 1),
        (if j = 0 then D y / y else D (x j) - D y / y) • v j) = 0 := by
    calc
      _ = (D y / y) • v 0 +
          ∑ j : Fin m, (D (x j.succ) - D y / y) • v j.succ := by
        simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, ↓reduceIte]
      _ = (D y / y) • (y • u 0 + ∑ j : Fin m, u j.succ) +
          ∑ j : Fin m, (D (x j.succ) - D y / y) • u j.succ := by
        simp only [hvzero, hvsucc]
      _ = D y • u 0 + ∑ j : Fin m, D (x j.succ) • u j.succ := by
        rw [smul_add, smul_smul, div_mul_cancel₀ _ hy, Finset.smul_sum]
        simp only [sub_smul, Finset.sum_sub_distrib]
        abel
      _ = 0 := by
        simpa only [Fin.sum_univ_succ] using hchain D
  by_cases hi : i = 0
  · refine ⟨0, ?_⟩
    intro D
    have hc := hpivot
      (fun j => if j = 0 then D y / y else D (x j) - D y / y)
      (hrelation D)
    have hz : D y / y = 0 := by
      simpa only [hi, ↓reduceIte] using hc
    simpa only [map_zero] using hz.symm
  · refine ⟨x i, ?_⟩
    intro D
    have hc := hpivot
      (fun j => if j = 0 then D y / y else D (x j) - D y / y)
      (hrelation D)
    have hz : D (x i) - D y / y = 0 := by
      simpa only [if_neg hi] using hc
    exact sub_eq_zero.mp hz