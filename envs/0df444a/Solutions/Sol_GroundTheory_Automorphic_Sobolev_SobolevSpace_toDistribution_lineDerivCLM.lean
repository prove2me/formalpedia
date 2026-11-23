-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:54.363813+00:00
-- url     : https://prove2.me/submissions/c0096abf-492e-4962-b8ec-11ebedba0a0d

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
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
open LineDeriv
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (v : E) (u : SobolevSpace E F s) :
    toDistribution (lineDerivCLM v u) = ∂_{v} (toDistribution u) := by
  rw [lineDerivCLM, toDistribution_multiplier, lineDeriv_eq_fourierMultiplierCLM]
  have h := fourierMultiplierCLM_smul (F := F) (g := fun x : E ↦ ((inner ℝ x v : ℝ) : ℂ))
    (by fun_prop) (2 * Real.pi * Complex.I)
  rw [← smul_apply, ← h]
  rfl
end GroundTheory.Automorphic.Sobolev.SobolevSpace
