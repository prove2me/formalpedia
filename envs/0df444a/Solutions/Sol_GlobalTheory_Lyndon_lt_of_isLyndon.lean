-- Prove2me | solution 1 for GlobalTheory.Lyndon.lt_of_isLyndon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:19.708914+00:00
-- url     : https://prove2.me/submissions/538b5371-3bcf-4401-9eac-a55cfd71b3ab

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
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution {w : List A} (h : IsLyndon w) {u v : List A} (hu : u ≠ []) (hv : v ≠ [])
    (e : w = u ++ v) : w < v := h.2 u v hu hv e
end GlobalTheory.Lyndon
