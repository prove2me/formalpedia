-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fraction_field_finite_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:52:06.680551+00:00
-- url     : https://prove2.me/submissions/73dd3832-9328-420e-93bb-dbae8da4d2f3

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] :
    Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) < Cardinal.aleph0 := by
  classical
  set K := logarithmicPrimeField P
  set R := MvPolynomial (Fin (m + 1)) Complex
  set A := R ⧸ P
  let x : Fin (m + 1) → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin Complex t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap Complex K a from
        (IsScalarTower.algebraMap_apply Complex R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin Complex t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Complex t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin Complex t := ⟨_, hA a⟩
    let b' : Algebra.adjoin Complex t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  refine lt_of_le_of_lt (Algebra.IsAlgebraic.trdeg_le_cardinalMk Complex t) ?_
  exact (Set.finite_range x).lt_aleph0
