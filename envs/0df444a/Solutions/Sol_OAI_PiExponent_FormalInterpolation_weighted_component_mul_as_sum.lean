-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mul_as_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:39:31.524854+00:00
-- url     : https://prove2.me/submissions/9b2d9ac3-3667-4041-8c38-ba7f2353d4ec

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Real) (D E : Real)
    (q f : MvPolynomial (Fin d) Complex)
    (hf : MvPolynomial.IsWeightedHomogeneous w f D) :
    MvPolynomial.weightedHomogeneousComponent w E (q * f) =
      ∑ a ∈ insert (E - D) (q.support.image (Finsupp.weight w)),
        if a + D = E then
          MvPolynomial.weightedHomogeneousComponent w a q * f
        else 0 := by
  classical
  let s : Finset Real := q.support.image (Finsupp.weight w)
  let c : Real := E - D
  have hs :
      Function.support (fun a : Real =>
        MvPolynomial.weightedHomogeneousComponent w a q) ⊆ (s : Set Real) := by
    intro a ha
    change MvPolynomial.weightedHomogeneousComponent w a q ≠ 0 at ha
    change a ∈ s
    by_contra hnot
    exact ha (MvPolynomial.weightedHomogeneousComponent_eq_zero_of_notMem w q a hnot)
  have hq :
      q = ∑ a ∈ s, MvPolynomial.weightedHomogeneousComponent w a q := by
    calc
      q = finsum (fun a : Real => MvPolynomial.weightedHomogeneousComponent w a q) :=
        (MvPolynomial.sum_weightedHomogeneousComponent w q).symm
      _ = ∑ a ∈ s, MvPolynomial.weightedHomogeneousComponent w a q :=
        finsum_eq_sum_of_support_subset _ hs
  have hterm (a : Real) :
      MvPolynomial.weightedHomogeneousComponent w E
          (MvPolynomial.weightedHomogeneousComponent w a q * f) =
        if a + D = E then
          MvPolynomial.weightedHomogeneousComponent w a q * f
        else 0 := by
    by_cases h : a + D = E
    · rw [if_pos h, ← h]
      exact MvPolynomial.weightedHomogeneousComponent_eq_self
        ((MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous a q).mul hf)
    · rw [if_neg h]
      exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
        E ((MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous a q).mul hf)
        (Ne.symm h)
  have hcadd : c + D = E := by
    dsimp [c]
    exact sub_add_cancel E D
  have hindex (a : Real) : a + D = E ↔ a = c := by
    constructor
    · intro h
      dsimp [c]
      linarith
    · intro h
      dsimp [c] at h
      rw [h]
      exact hcadd
  conv_lhs => rw [hq, Finset.sum_mul, map_sum]
  simp_rw [hterm]
  by_cases hc : c ∈ s
  · rw [Finset.insert_eq_of_mem hc]
  · rw [Finset.sum_insert hc]
    have hzero :
        (∑ a ∈ s,
          (if a + D = E then
            MvPolynomial.weightedHomogeneousComponent w a q * f
          else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hne : a + D ≠ E := by
        intro h
        apply hc
        have hac : a = c := (hindex a).mp h
        rw [← hac]
        exact ha
      simp [hne]
    have hz : MvPolynomial.weightedHomogeneousComponent w c q = 0 :=
      MvPolynomial.weightedHomogeneousComponent_eq_zero_of_notMem w q c hc
    simp [hcadd, hz, hzero]