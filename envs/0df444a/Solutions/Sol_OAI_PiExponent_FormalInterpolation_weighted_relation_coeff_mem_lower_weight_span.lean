-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_mem_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:09:47.168132+00:00
-- url     : https://prove2.me/submissions/ae33422e-7a64-4050-a64d-65803c1d3324

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_coeff_nat_weight_lt
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_lt_mem_lower_weight_span

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (delta : Nat) (hdelta : 0 < delta) (n : Nat) (i : Fin d) (q : MvPolynomial (Fin d) ℂ) (hq : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - (delta : ℤ)) : q ∈ Submodule.span ℂ {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
  apply OAI.PiExponent.FormalInterpolation.support_lt_mem_lower_weight_span W (n * W i) q
  exact OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_nat_weight_lt W delta hdelta n i q hq