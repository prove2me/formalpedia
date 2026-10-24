-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mul_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:40:42.311369+00:00
-- url     : https://prove2.me/submissions/1561456f-40bf-4a05-8a0f-c851980c4caa

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open MvPolynomial

theorem solution
    {d : Nat} (w : Fin d → ℚ) (D N : ℚ)
    (a b : MvPolynomial (Fin d) ℂ)
    (hb : MvPolynomial.IsWeightedHomogeneous w b D) :
    MvPolynomial.weightedHomogeneousComponent w N (a * b) =
      ∑ᶠ m : ℚ, if m + D = N then
        MvPolynomial.weightedHomogeneousComponent w m a * b else 0 := by
  let L : MvPolynomial (Fin d) ℂ →+ MvPolynomial (Fin d) ℂ :=
    { toFun := fun p =>
        MvPolynomial.weightedHomogeneousComponent w N (p * b)
      map_zero' := by simp
      map_add' := by
        intro p q
        simp only [add_mul, map_add] }
  have hexpand :
      MvPolynomial.weightedHomogeneousComponent w N (a * b) =
        ∑ᶠ m : ℚ, MvPolynomial.weightedHomogeneousComponent w N
          (MvPolynomial.weightedHomogeneousComponent w m a * b) := by
    have h := congrArg L (MvPolynomial.sum_weightedHomogeneousComponent w a)
    have hs := h.symm
    rw [L.map_finsum (MvPolynomial.weightedHomogeneousComponent_finsupp (w := w) (φ := a))] at hs
    change MvPolynomial.weightedHomogeneousComponent w N (a * b) =
      ∑ᶠ m : ℚ, MvPolynomial.weightedHomogeneousComponent w N
        (MvPolynomial.weightedHomogeneousComponent w m a * b) at hs
    exact hs
  rw [hexpand]
  apply finsum_congr
  intro m
  have hm : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.weightedHomogeneousComponent w m a * b) (m + D) :=
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) (n := m) a).mul hb
  by_cases h : m + D = N
  · subst N
    simp [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hm]
  · rw [if_neg h]
    rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
      (w := w) (m := m + D) (n := N)
      (p := MvPolynomial.weightedHomogeneousComponent w m a * b)
      hm (Ne.symm h)]