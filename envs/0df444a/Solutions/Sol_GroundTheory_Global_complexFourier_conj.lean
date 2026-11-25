-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:00.041804+00:00
-- url     : https://prove2.me/submissions/f0f4796b-29b3-41f5-b4e9-76b0bf775a8b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (f : ℂ → ℂ) (w : ℂ) :
    complexFourier (fun z ↦ conj (f z)) w = conj (complexFourier f (-w)) := by
  rw [complexFourier, complexFourier, ← integral_conj]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Real.fourierChar_apply, ← exp_conj]
  congr 2
  simp only [conj_ofReal, conj_I]
  push_cast
  simp only [neg_mul, mul_neg, neg_re, mul_re, ofReal_neg, ofReal_sub, ofReal_mul]
  ring
end GroundTheory.Global
