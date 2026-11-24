-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.norm_cexp_neg_two_pi_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:06.634588+00:00
-- url     : https://prove2.me/submissions/10763b05-8481-4307-a4b6-d85f17f847c4

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
theorem _root_.solution (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp
end GlobalTheory.LinPhaseSeminorm
