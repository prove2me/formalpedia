-- Prove2me | solution 1 for GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:15.166252+00:00
-- url     : https://prove2.me/submissions/d98aa561-3039-4fda-b864-37667b6fed1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBoundedStatement
import Theorems.Thm_GlobalTheory_HeckeTheta_GaussBound_gauss_cont_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | exact GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | (intros; apply GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound <;> assumption)
end _root_.GlobalTheory.T
