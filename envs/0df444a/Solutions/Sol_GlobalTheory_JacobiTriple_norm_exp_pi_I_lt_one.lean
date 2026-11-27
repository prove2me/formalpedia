-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.norm_exp_pi_I_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:43.399699+00:00
-- url     : https://prove2.me/submissions/a2a15157-1eaf-467f-80d6-52fe7b4ef813

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution (τ : ℂ) (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith
end GlobalTheory.JacobiTriple
