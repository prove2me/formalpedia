-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.weight_smul_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:54.402526+00:00
-- url     : https://prove2.me/submissions/45755b8a-5e13-45db-a94c-0d095891f0b2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

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
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) (ξ : E) :
    weight s ξ • fourierFun u ξ = (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) ξ := by
  rw [fourierFun, smul_smul, weight_mul_weight]; simp [weight]
end GroundTheory.Automorphic.Sobolev
