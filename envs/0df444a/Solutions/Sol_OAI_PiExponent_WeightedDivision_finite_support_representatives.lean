-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.finite_support_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:43:06.655518+00:00
-- url     : https://prove2.me/submissions/748b291f-4c61-4498-954e-f35ca5bf69b5

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (F : MvPolynomial ι R)
    (hF : ∀ v ∈ F.support,
      ∃ Q : MvPolynomial ι R,
        MvPolynomial.monomial v (1 : R) - Q ∈ J ∧
          ∀ w ∈ Q.support, A w) :
    ∃ Q : MvPolynomial ι R,
      F - Q ∈ J ∧ ∀ w ∈ Q.support, A w := by
  classical
  let q : (ι →₀ ℕ) → MvPolynomial ι R := fun v =>
    if hv : v ∈ F.support then Classical.choose (hF v hv) else 0
  have hq (v : ι →₀ ℕ) (hv : v ∈ F.support) :
      MvPolynomial.monomial v (1 : R) - q v ∈ J ∧
        ∀ w ∈ (q v).support, A w := by
    dsimp [q]
    rw [dif_pos hv]
    exact Classical.choose_spec (hF v hv)
  let Q : MvPolynomial ι R :=
    ∑ v ∈ F.support, (MvPolynomial.coeff v F) • q v
  refine ⟨Q, ?_, ?_⟩
  · have hsum :
        (∑ v ∈ F.support,
          (MvPolynomial.monomial v (MvPolynomial.coeff v F) -
            MvPolynomial.C (MvPolynomial.coeff v F) * q v)) ∈ J := by
      apply Submodule.sum_mem
      intro v hv
      have hqv := hq v hv
      have hident :
          MvPolynomial.monomial v (MvPolynomial.coeff v F) =
            MvPolynomial.C (MvPolynomial.coeff v F) *
              MvPolynomial.monomial v (1 : R) := by
        rw [MvPolynomial.C_mul_monomial]
        simp
      have hmul :
          MvPolynomial.C (MvPolynomial.coeff v F) *
              (MvPolynomial.monomial v (1 : R) - q v) ∈ J :=
        J.mul_mem_left _ hqv.1
      rw [hident]
      convert hmul using 1 <;> ring
    have hEq :
        F - Q =
          ∑ v ∈ F.support,
            (MvPolynomial.monomial v (MvPolynomial.coeff v F) -
              MvPolynomial.C (MvPolynomial.coeff v F) * q v) := by
      rw [Finset.sum_sub_distrib]
      apply congrArg₂ (fun p r : MvPolynomial ι R => p - r)
      · exact (MvPolynomial.support_sum_monomial_coeff F).symm
      · change (∑ v ∈ F.support, (MvPolynomial.coeff v F) • q v) =
          ∑ v ∈ F.support, MvPolynomial.C (MvPolynomial.coeff v F) * q v
        apply Finset.sum_congr rfl
        intro v hv
        exact MvPolynomial.smul_eq_C_mul (q v) (MvPolynomial.coeff v F)
    rw [hEq]
    exact hsum
  · intro w hw
    have hw' : w ∈ F.support.biUnion fun v => ((MvPolynomial.coeff v F) • q v).support :=
      MvPolynomial.support_sum hw
    rcases Finset.mem_biUnion.mp hw' with ⟨v, hv, hwv⟩
    have hwq : w ∈ (q v).support := MvPolynomial.support_smul hwv
    exact (hq v hv).2 w hwq