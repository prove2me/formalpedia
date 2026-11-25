-- Prove2me | solution 1 for GroundTheory.Global.complexGaussian_neg_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:03.049294+00:00
-- url     : https://prove2.me/submissions/574cbc14-4130-44c2-856a-1a76fc444cc6

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
theorem _root_.solution (n : ℕ) :
    complexGaussian (-(n : ℤ)) = fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  rw [complexGaussian]
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp
  · simp
end GroundTheory.Global
