-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integrable_fourierFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:50.992871+00:00
-- url     : https://prove2.me/submissions/31d54199-de89-4c7e-a972-9ec0fd6ed722

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_pow_mul_norm_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (u : SobolevSpace E F s) : Integrable (fourierFun u) (volume : Measure E) := by
  have h := integrable_pow_mul_norm_fourierFun (j := 0) (by simpa using hs) u
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (fourierFun_aestronglyMeasurable u)).1 h
end GroundTheory.Automorphic.Sobolev
