-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_sorted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:45.683978+00:00
-- url     : https://prove2.me/submissions/17320b7b-0e40-4062-84cb-626f927fcd11

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
theorem _root_.solution (S : Multiset (List A)) :
    ∃ Q : List (List A), (Q : Multiset (List A)) = S ∧ Q.Pairwise (· ≥ ·) :=
  ⟨S.sort (· ≥ ·), Multiset.sort_eq _ _, Multiset.pairwise_sort _ _⟩
end GlobalTheory.Lyndon
