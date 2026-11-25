-- Prove2me | solution 1 for GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:09.879506+00:00
-- url     : https://prove2.me/submissions/eb41a712-d69a-4794-ae23-95219f5a2105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistedTraceEquivariantAndInjectiveOfGroupDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi
end GlobalTheory
