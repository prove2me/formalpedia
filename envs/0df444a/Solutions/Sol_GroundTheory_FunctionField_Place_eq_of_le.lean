-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:50.059803+00:00
-- url     : https://prove2.me/submissions/598b18b2-7f4b-4fd0-a69e-817a396ea39b

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution [IsFunctionField k K] {v w : Place k K} (h : v.ring ≤ w.ring) : v = w := by
  ext1
  have key : ∀ (P : Ideal v.ring) [P.IsPrime], v.ring.ofPrime P = w.ring → v.ring = w.ring := by
    intro P hP hPw
    rcases eq_or_ne P ⊥ with h0 | h0
    · subst h0
      rw [ValuationSubring.ofPrime_bot] at hPw
      exact absurd hPw.symm w.ne_top
    · have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP h0
      have hm := IsLocalRing.eq_maximalIdeal hmax
      subst hm
      rw [ValuationSubring.ofPrime_top] at hPw
      exact hPw
  exact key _ (v.ring.ofPrime_idealOfLE w.ring h)
end GroundTheory.FunctionField.Place
