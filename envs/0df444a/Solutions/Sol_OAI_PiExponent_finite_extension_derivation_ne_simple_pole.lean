-- Prove2me | solution 1 for OAI.PiExponent.finite_extension_derivation_ne_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:28:59.309045+00:00
-- url     : https://prove2.me/submissions/cf966bae-df6b-47cd-bd99-fe1b9b6956e7

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

import Theorems.Thm_OAI_PiExponent_derivation_trace_of_basis
import Theorems.Thm_OAI_PiExponent_ratFunc_derivation_ne_simple_pole
namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open Polynomial
open OAI.PiExponent

theorem solution
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by
  intro hx
  have ht := derivation_trace_of_basis d D hcompat
    (Module.finBasis (RatFunc K) E) x
  rw [hx, Algebra.trace_algebraMap] at ht
  have hdegree : (Module.finrank (RatFunc K) E : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
  apply ratFunc_derivation_ne_simple_pole d hdX (Algebra.trace (RatFunc K) E x)
    (mul_ne_zero hdegree hc)
  calc
    d (Algebra.trace (RatFunc K) E x) =
        Module.finrank (RatFunc K) E • (RatFunc.C c / RatFunc.X) := ht
    _ = RatFunc.C ((Module.finrank (RatFunc K) E : K) * c) / RatFunc.X := by
      simp only [map_mul, map_natCast, nsmul_eq_mul, mul_div_assoc]
