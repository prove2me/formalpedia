-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_support_product_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:08:06.938789+00:00
-- url     : https://prove2.me/submissions/ed5aa0dd-41f2-408f-b759-a46e1e119c57

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_prod_exponents
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_exp_sum_bound
open scoped BigOperators

theorem solution {d : Nat} (w : Fin d → Rat) (q : Rat) (m : Nat)
    (v : Fin m → MvPolynomial (Fin d) Complex)
    (hv : ∀ i a, a ∈ (v i).support →
      ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) :
    ∀ a ∈ (∏ i, v i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ ((q * (m : Rat) : Rat) : Real) := by
  intro a ha
  obtain ⟨b, hb, hsum⟩ :=
    OAI.PiExponent.FormalInterpolation.support_prod_exponents (v := v) (a := a) ha
  exact OAI.PiExponent.FormalInterpolation.weighted_exp_sum_bound
    (w := w) (q := q) (b := b) (a := a) (hsum := hsum)
    (hb := fun i => hv i (b i) (hb i))