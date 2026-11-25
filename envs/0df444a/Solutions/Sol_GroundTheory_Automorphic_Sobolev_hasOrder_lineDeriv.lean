-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_lineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:33.174472+00:00
-- url     : https://prove2.me/submissions/3c88fbe2-a620-431d-9d60-0cc2d143843b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_lineDeriv_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (v : E) : HasOrder (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v) 1 := fun s ↦
  ⟨2 * Real.pi * ‖v‖, by positivity, fun u hu ↦ sob_lineDeriv_le v hu⟩
end GroundTheory.Automorphic.Sobolev
