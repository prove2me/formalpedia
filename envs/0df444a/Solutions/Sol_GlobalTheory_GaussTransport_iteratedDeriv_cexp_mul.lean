-- Prove2me | solution 1 for GlobalTheory.GaussTransport.iteratedDeriv_cexp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:59.154677+00:00
-- url     : https://prove2.me/submissions/ec293c67-fbde-478d-961c-b78a03f150d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport
namespace GlobalTheory.GaussTransport
theorem _root_.solution (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring
end GlobalTheory.GaussTransport
