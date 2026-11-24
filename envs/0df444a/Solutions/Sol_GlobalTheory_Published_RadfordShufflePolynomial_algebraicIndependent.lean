-- Prove2me | solution 1 for GlobalTheory.Published.RadfordShufflePolynomial.algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:37.348813+00:00
-- url     : https://prove2.me/submissions/a378d916-6481-4393-a285-3f127dd2f27a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Published
namespace GlobalTheory.Published
namespace RadfordShufflePolynomial
theorem _root_.solution (h : RadfordShufflePolynomial)
    (K : Type) [Field K] [CharZero K] (A : Type) [LinearOrder A] :
    AlgebraicIndependent K
      (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word K l.1) :=
  (h K A).1
end RadfordShufflePolynomial
end GlobalTheory.Published
