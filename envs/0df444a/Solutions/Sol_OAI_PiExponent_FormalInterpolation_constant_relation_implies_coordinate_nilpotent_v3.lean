-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_relation_implies_coordinate_nilpotent_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:48:00.610693+00:00
-- url     : https://prove2.me/submissions/de97f07a-fb28-4ef4-b9b5-cef3acf261b0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ, MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (i : Fin d) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hpI : Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I)
    (hdeg : ¬ 0 < p.natDegree) :
    ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by
  have hpconst : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hdeg)
  have hcoeff : p.coeff 0 ≠ 0 := by
    intro hzero
    have hC : Polynomial.C (p.coeff 0) = 0 := by
      rw [hzero]
      exact map_zero _
    exact hp (hpconst.trans hC)
  have hscalar : MvPolynomial.C (p.coeff 0) ∈ I := by
    rw [hpconst] at hpI
    simpa only [Polynomial.eval₂_C] using hpI
  have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : MvPolynomial (Fin d) ℂ) :=
    IsUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ)
      (isUnit_iff_ne_zero.mpr hcoeff)
  have htop : I = ⊤ := I.eq_top_of_isUnit_mem hscalar hunit
  refine ⟨1, by norm_num, ?_⟩
  rw [htop]
  simp