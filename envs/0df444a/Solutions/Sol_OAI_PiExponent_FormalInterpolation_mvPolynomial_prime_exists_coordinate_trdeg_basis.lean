-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_exists_coordinate_trdeg_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:46:36.440395+00:00
-- url     : https://prove2.me/submissions/b97b1c5a-2504-4003-9701-2676c48864b8

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ∃ s : Finset (Fin (m + 1)),
      AlgebraicIndependent Complex
        (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (logarithmicPrimeField P) (MvPolynomial.X i.1)) ∧
      s.card = (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
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
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := Complex) t
  have hfin : u.Finite := (Set.finite_range x).subset hut
  have hpre : ∀ y : u, ∃ i, x i = y.1 := fun y => hut y.2
  let g : u → Fin (m + 1) := fun y => Classical.choose (hpre y)
  have hg : ∀ y, x (g y) = y.1 := fun y => Classical.choose_spec (hpre y)
  have ginj : Function.Injective g := by
    intro y z h; apply Subtype.ext; rw [← hg y, ← hg z, h]
  haveI : Fintype u := hfin.fintype
  set S : Finset (Fin (m + 1)) := Finset.univ.image g with hS
  refine ⟨S, ?_, ?_⟩
  · have hmemu : ∀ i : S, x i.1 ∈ u := by
      intro ⟨i, hi⟩
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hi)
      simpa [hg y] using y.2
    let f : S → u := fun i => ⟨x i.1, hmemu i⟩
    have finj : Function.Injective f := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hi)
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hj)
      have : x (g y) = x (g z) := congrArg Subtype.val h
      rw [hg, hg] at this
      have : y = z := Subtype.ext this
      subst this; rfl
    exact hu.1.comp f finj
  · rw [hS, Finset.card_image_of_injective _ ginj, Finset.card_univ]
    have := hu.cardinalMk_eq_trdeg
    rw [← this, Cardinal.mk_fintype, Cardinal.toNat_natCast]
