-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_reflect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:23.662802+00:00
-- url     : https://prove2.me/submissions/05295753-bf74-4275-a9c5-fc27147ca85a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (ψ : 𝓢(E, ℂ)) (x : E) : 𝓕 (reflect E ψ) x = 𝓕 ψ (-x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) ψ x
end GroundTheory.Automorphic.Sobolev
