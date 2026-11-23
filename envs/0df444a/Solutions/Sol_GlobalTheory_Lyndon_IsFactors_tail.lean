-- Prove2me | solution 1 for GlobalTheory.Lyndon.IsFactors.tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:13.561772+00:00
-- url     : https://prove2.me/submissions/1e6d2d82-3a0b-4c69-829c-fbe507700454

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
namespace IsFactors
theorem _root_.solution {l : List A} {L : List (List A)} (h : IsFactors (l :: L)) : IsFactors L :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 h.2).2⟩
end IsFactors
end GlobalTheory.Lyndon
