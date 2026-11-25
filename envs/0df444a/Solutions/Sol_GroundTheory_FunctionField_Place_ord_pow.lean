-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ord_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:09.433802+00:00
-- url     : https://prove2.me/submissions/d27cb709-6829-4a54-b1ee-c5a5fb12af92

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (x : K) (n : ℕ) : v.ord (x ^ n) = n * v.ord x := by
  by_cases hx : x = 0
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp [hx, zero_pow hn.ne']
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring
end GroundTheory.FunctionField.Place
