-- Prove2me | solution 1 for GlobalTheory.Lyndon.repr_sum_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:45.951434+00:00
-- url     : https://prove2.me/submissions/567af831-906a-44d0-b37d-b1b2c3245390

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
open ShuffleAlgebra
variable (K : Type) [Field K]
namespace GlobalTheory.Lyndon
theorem _root_.solution (s : Multiset (List A)) (w : List A) :
    (wordBasis K A).repr (s.map (word K)).sum w = (s.count w : K) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, map_add, Finsupp.add_apply, ih,
      ← wordBasis_apply, Module.Basis.repr_self, Multiset.count_cons, Finsupp.single_apply]
    by_cases h : x = w
    · simp [h, add_comm]
    · simp [h, Ne.symm h]
end GlobalTheory.Lyndon
