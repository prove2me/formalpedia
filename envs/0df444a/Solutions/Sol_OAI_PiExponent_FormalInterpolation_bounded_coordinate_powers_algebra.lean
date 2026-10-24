-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:50:32.963847+00:00
-- url     : https://prove2.me/submissions/21d73bcf-6d4f-440b-8ead-ba5272de9119

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (s : Nat) (hs : 0 < s) (B : Nat)
    (q D : Nat) (hq : 0 < q) (hDpos : 0 < D)
    (hDcut : (D : Real) < ((s * q : Nat) : Real) * R)
    (hcommon : ∀ i : Fin d, ∃ n : Nat, ∃ m : Nat,
      0 < n ∧ MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) ≤ (B : Real) ∧
      q * n ≤ m ∧ 0 < m ∧
      (m : Real) * (w i : Real) = (D : Real)) :
    ∃ s' : Nat, 0 < s' ∧ ∃ D' : Nat,
      (D' : Real) < (s' : Real) * R ∧
      0 < D' ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s' ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (D' : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D' : ℚ) g} := by
  refine ⟨s * q, Nat.mul_pos hs hq, D, ?_, hDpos, ?_⟩
  · simpa [Nat.cast_mul] using hDcut
  · intro i
    rcases hcommon i with ⟨n, m, hn, hxn, hnB, hnm, hm, hdegree⟩
    refine ⟨m, hm, ?_⟩
    let g : MvPolynomial (Fin d) Complex := MvPolynomial.X i ^ m
    have hpow : (MvPolynomial.X i ^ n) ^ q ∈ (I ^ s) ^ q :=
      Ideal.pow_mem_pow hxn q
    have hpow' : MvPolynomial.X i ^ (n * q) ∈ I ^ (s * q) := by
      simpa only [← pow_mul] using hpow
    have hnm' : n * q ≤ m := by
      simpa [Nat.mul_comm] using hnm
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hnm'
    have hm_eq : m = n * q + r := hr
    have hg : g ∈ I ^ (s * q) := by
      dsimp [g]
      rw [hm_eq, pow_add]
      exact (I ^ (s * q)).mul_mem_right _ hpow'
    have hbound : ∀ a ∈ g.support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real) := by
      intro a ha
      have ha' : a = Finsupp.single i m := by
        have hsupp : g.support = {Finsupp.single i m} := by
          simp [g, MvPolynomial.support_X_pow]
        rw [hsupp] at ha
        exact Finset.mem_singleton.mp ha
      subst a
      have hsum :
          (∑ k : Fin d, (w k : Real) *
            ((Finsupp.single i m : Fin d →₀ Nat) k : Real)) =
            (m : Real) * (w i : Real) := by
        simp [Finsupp.single_apply, mul_comm]
      rw [hsum]
      exact le_of_eq hdegree
    have hdegreeRat : (m : ℚ) * w i = (D : ℚ) := by
      exact_mod_cast hdegree
    have hcomponent :
        MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : ℚ)) (D : ℚ) g = g := by
      change MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : ℚ)) (D : ℚ) (MvPolynomial.X i ^ m) =
        MvPolynomial.X i ^ m
      apply MvPolynomial.weightedHomogeneousComponent_eq_self
      rw [MvPolynomial.X_pow_eq_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      simpa [Finsupp.weight_single] using hdegreeRat
    refine Ideal.subset_span ?_
    refine ⟨g, hg, hbound, ?_⟩
    simpa [g, hcomponent]
