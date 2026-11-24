-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:35.118808+00:00
-- url     : https://prove2.me/submissions/a2c417b1-6a25-4c9c-966e-33acd5857b2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm
namespace GlobalTheory.LinPhaseSeminorm
theorem _root_.solution (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := by
  induction n generalizing c with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => c * Complex.exp (a * y)) =
        fun y : ℝ => (c * a) * Complex.exp (a * y) := by
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y))
          (c * (Complex.exp (a * y) * (a * 1))) y :=
        ((h1.const_mul a).cexp).const_mul c
      rw [h.deriv]; ring
    rw [hd, ih]; funext y; ring
end GlobalTheory.LinPhaseSeminorm
