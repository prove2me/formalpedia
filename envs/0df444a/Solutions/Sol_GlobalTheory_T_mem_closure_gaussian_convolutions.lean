-- Prove2me | solution 1 for GlobalTheory.T.mem_closure_gaussian_convolutions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:32.247391+00:00
-- url     : https://prove2.me/submissions/5a45f90b-11ef-40db-9003-56746d7c0486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDenseStatement
import Theorems.Thm_GlobalTheory_narrowGauss_convolution_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  first | exact @GlobalTheory.narrowGauss_convolution_dense | exact GlobalTheory.narrowGauss_convolution_dense | (intros; apply GlobalTheory.narrowGauss_convolution_dense <;> assumption)
end _root_.GlobalTheory.T
