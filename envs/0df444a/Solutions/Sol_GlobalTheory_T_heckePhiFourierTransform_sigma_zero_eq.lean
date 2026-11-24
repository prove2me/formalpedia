-- Prove2me | solution 1 for GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:17.819329+00:00
-- url     : https://prove2.me/submissions/b2a9d3b1-9748-4bda-83f2-7f465de306f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEqStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_hTrans_sigma_zero_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq <;> assumption)
end _root_.GlobalTheory.T
