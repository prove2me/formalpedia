-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.locallyIntegrable_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:23.496881+00:00
-- url     : https://prove2.me/submissions/c1c64ec5-910c-4da4-a77a-94a207e982ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs

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
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    LocallyIntegrable (fourierFun u) (volume : Measure E) := by
  have hG := (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).locallyIntegrable
    (by norm_num)
  have := hG.continuous_smul (weight_hasTemperateGrowth (-s)).1.continuous
  exact this
end GroundTheory.Automorphic.Sobolev
