-- Prove2me | solution 1 for GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:24.794409+00:00
-- url     : https://prove2.me/submissions/23215e07-46f8-480e-bc6f-d805476cec4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
import Theorems.Thm_GlobalTheory_GaussCutoff_mem_closure_gauss_mul


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
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  first | exact @GlobalTheory.GaussCutoff.mem_closure_gauss_mul | exact GlobalTheory.GaussCutoff.mem_closure_gauss_mul | (intros; apply GlobalTheory.GaussCutoff.mem_closure_gauss_mul <;> assumption)
end _root_.GlobalTheory.T
