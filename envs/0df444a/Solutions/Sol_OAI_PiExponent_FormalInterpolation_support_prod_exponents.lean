-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_prod_exponents
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:14:41.642977+00:00
-- url     : https://prove2.me/submissions/949093ac-1163-439a-b56d-9f82910c3957

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_finset_prod_exponents
open scoped BigOperators

theorem solution {d m : Nat} (v : Fin m → MvPolynomial (Fin d) Complex)
    (a : Fin d →₀ Nat) (ha : a ∈ (∏ i, v i).support) :
    ∃ b : Fin m → (Fin d →₀ Nat), (∀ i, b i ∈ (v i).support) ∧ (∑ i, b i) = a := by
  classical
  simpa using
    (OAI.PiExponent.FormalInterpolation.support_finset_prod_exponents
      (s := Finset.univ) (v := v) (a := a) ha)