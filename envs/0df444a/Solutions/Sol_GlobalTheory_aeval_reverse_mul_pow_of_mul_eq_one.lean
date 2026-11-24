-- Prove2me | solution 1 for GlobalTheory.aeval_reverse_mul_pow_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:09.334852+00:00
-- url     : https://prove2.me/submissions/3e17d43c-7e6f-4e08-9e9d-a8d354b571f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x y : B) (h : x * y = 1) (P : k[X]) :
    aeval y P.reverse * x ^ P.natDegree = aeval x P := by
  letI : Invertible x := invertibleOfRightInverse x y h
  have hinv : (⅟x : B) = y := invOf_eq_right_inv h
  have := eval₂_reverse_mul_pow (algebraMap k B) x P
  rw [hinv] at this
  simpa [aeval_def] using this
end GlobalTheory
