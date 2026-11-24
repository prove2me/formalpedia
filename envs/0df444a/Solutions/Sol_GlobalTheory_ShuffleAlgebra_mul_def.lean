-- Prove2me | solution 1 for GlobalTheory.ShuffleAlgebra.mul_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:09.601861+00:00
-- url     : https://prove2.me/submissions/00b8583a-8929-42a3-aa36-150551cb79db

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
theorem _root_.solution (x y : ShuffleAlgebra K A) : x * y = mulLin K x y := rfl
end GlobalTheory.ShuffleAlgebra
