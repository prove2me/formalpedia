-- Prove2me | solution 1 for GlobalTheory.ShuffleAlgebra.word_mul_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:40.235583+00:00
-- url     : https://prove2.me/submissions/09ccf7b7-859f-469f-93b5-1815907ad671

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
open GlobalTheory.ShuffleAlgebra
variable (K : Type) [CommRing K] {A : Type}
namespace GlobalTheory.ShuffleAlgebra
theorem _root_.solution (u v : List A) :
    word K u * word K v = ((shuffle u v).map (word K)).sum := mulLin_word K u v
end GlobalTheory.ShuffleAlgebra
