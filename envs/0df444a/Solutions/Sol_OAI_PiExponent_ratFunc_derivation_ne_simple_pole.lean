-- Prove2me | solution 1 for OAI.PiExponent.ratFunc_derivation_ne_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:28:19.517967+00:00
-- url     : https://prove2.me/submissions/9e2676a5-5b1f-4497-885c-187c07a06acb

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

import Theorems.Thm_OAI_PiExponent_ratFunc_derivation_polynomial
import Theorems.Thm_OAI_PiExponent_polynomial_logarithmic_equation_impossible
namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open Polynomial
open OAI.PiExponent

theorem solution {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by
  intro heq
  have hquot := D.leibniz_div (algebraMap K[X] (RatFunc K) r.num)
    (algebraMap K[X] (RatFunc K) r.denom)
  rw [RatFunc.num_div_denom, ratFunc_derivation_polynomial D hDX,
    ratFunc_derivation_polynomial D hDX] at hquot
  have hder : D r =
      algebraMap K[X] (RatFunc K) (derivative r.num * r.denom - r.num * derivative r.denom) /
        (algebraMap K[X] (RatFunc K) r.denom) ^ 2 := by
    rw [hquot]
    simp only [smul_eq_mul, map_sub, map_mul, div_eq_mul_inv, inv_pow]
    ring
  have hden : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero X_ne_zero
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hden) hx).mp (hder.symm.trans heq)
  apply polynomial_logarithmic_equation_impossible r.num r.denom r.denom_ne_zero
    r.isCoprime_num_denom hc
  apply RatFunc.algebraMap_injective K
  simpa only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, mul_comm] using hcross
