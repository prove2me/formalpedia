-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.positive_degree_relation_implies_coordinate_nilpotent_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:51:54.542312+00:00
-- url     : https://prove2.me/submissions/ffedec02-6ef5-43e5-9de8-1499364bb863

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

private theorem weighted_component_eval_coordinate
    {d : Nat} (w : Fin d → ℚ)
    (hw : ∀ j, 0 < (w j : ℝ))
    (i : Fin d) (p : Polynomial ℂ) (k : Nat) :
    MvPolynomial.weightedHomogeneousComponent w ((k : ℚ) * w i)
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p) =
      MvPolynomial.C (p.coeff k) * (MvPolynomial.X i) ^ k := by
  classical
  have hpow (e : Nat) :
      ((MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ e).IsWeightedHomogeneous w
        ((e : ℚ) * w i) := by
    convert (MvPolynomial.isWeightedHomogeneous_X ℂ w i).pow e using 1 <;>
      simp [nsmul_eq_mul]
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [map_sum]
  by_cases hk : k ∈ p.support
  · rw [Finset.sum_eq_single k]
    · simp only [MvPolynomial.weightedHomogeneousComponent_C_mul]
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (hpow k)]
    · intro e he hek
      have hweight : ((k : ℚ) * w i) ≠ (e : ℚ) * w i := by
        intro h
        have heq : (k : ℚ) = e := mul_right_cancel₀
          (ne_of_gt (show 0 < w i by exact_mod_cast hw i)) h
        exact hek (by exact_mod_cast heq.symm)
      simp only [MvPolynomial.weightedHomogeneousComponent_C_mul]
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ (hpow e) hweight]
      simp
    · exact fun hnot => (hnot hk).elim
  · have hcoeff : p.coeff k = 0 := by
      by_contra h
      exact hk (Polynomial.mem_support_iff.mpr h)
    rw [Finset.sum_eq_zero]
    · simp [hcoeff]
    · intro e he
      by_cases hek : e = k
      · subst e
        simp [hcoeff]
      · have hweight : ((k : ℚ) * w i) ≠ (e : ℚ) * w i := by
          intro h
          have heq : (k : ℚ) = e := mul_right_cancel₀
            (ne_of_gt (show 0 < w i by exact_mod_cast hw i)) h
          exact hek (by exact_mod_cast heq.symm)
        simp only [MvPolynomial.weightedHomogeneousComponent_C_mul]
        rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ (hpow e) hweight]
        simp

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ, MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (i : Fin d) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hpI : Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I)
    (hdeg : 0 < p.natDegree) :
    ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by
  refine ⟨p.natDegree, hdeg, ?_⟩
  have htop := hcomponents _ hpI ((p.natDegree : ℚ) * w i)
  rw [weighted_component_eval_coordinate w hw i p p.natDegree] at htop
  have hcoeff : p.coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hscale : MvPolynomial.C ((p.coeff p.natDegree)⁻¹) *
      (MvPolynomial.C (p.coeff p.natDegree) * (MvPolynomial.X i) ^ p.natDegree) ∈ I :=
    I.mul_mem_left _ htop
  have hscalar :
      (MvPolynomial.C ((p.coeff p.natDegree)⁻¹) : MvPolynomial (Fin d) ℂ) *
        (MvPolynomial.C (p.coeff p.natDegree) : MvPolynomial (Fin d) ℂ) =
        (1 : MvPolynomial (Fin d) ℂ) := by
    simpa only [map_mul, map_one] using
      (congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ)
        (inv_mul_cancel₀ hcoeff))
  have hcancel :
      MvPolynomial.C ((p.coeff p.natDegree)⁻¹) *
        (MvPolynomial.C (p.coeff p.natDegree) * (MvPolynomial.X i) ^ p.natDegree) =
      (MvPolynomial.X i) ^ p.natDegree := by
    calc
      _ = (MvPolynomial.C ((p.coeff p.natDegree)⁻¹) *
          MvPolynomial.C (p.coeff p.natDegree)) *
          (MvPolynomial.X i) ^ p.natDegree := by rw [mul_assoc]
      _ = 1 * (MvPolynomial.X i) ^ p.natDegree := by rw [hscalar]
      _ = _ := one_mul _
  rw [hcancel] at hscale
  exact hscale
