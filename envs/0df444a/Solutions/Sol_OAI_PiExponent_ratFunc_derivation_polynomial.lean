-- Prove2me | solution 1 for OAI.PiExponent.ratFunc_derivation_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:27:08.287973+00:00
-- url     : https://prove2.me/submissions/f7f4a6a1-476a-498d-ad11-76443543e842

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic


namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open Polynomial
open OAI.PiExponent

theorem solution {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by
  simpa [RatFunc.aeval_X_left_eq_algebraMap, hDX] using D.comp_aeval_eq RatFunc.X p
