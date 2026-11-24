-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.deriv_affine_cexp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:36.25982+00:00
-- url     : https://prove2.me/submissions/484c4a33-ca61-469d-a604-453a4872980b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution (a c d e : ℂ) :
    deriv (fun y : ℝ => c * Complex.exp (a * y) + d * y + e) =
      fun y : ℝ => c * a * Complex.exp (a * y) + d := by
  funext y
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y) + d * y + e)
      (c * (Complex.exp (a * y) * (a * 1)) + d * 1) y :=
    ((((h1.const_mul a).cexp).const_mul c).add (h1.const_mul d)).add_const e
  rw [h.deriv]; ring
end GlobalTheory.CharFormDeriv
