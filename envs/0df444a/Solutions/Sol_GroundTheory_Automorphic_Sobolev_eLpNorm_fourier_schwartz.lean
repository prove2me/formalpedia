-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.eLpNorm_fourier_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:18.336457+00:00
-- url     : https://prove2.me/submissions/740d6fcb-9039-4eb3-bf85-aa5318263100

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (f : 𝓢(E, ℂ)) :
    eLpNorm (𝓕 f : 𝓢(E, ℂ)) 2 volume = eLpNorm f 2 volume := by
  have h : ‖(𝓕 f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)‖ = ‖f.toLp 2 (volume : Measure E)‖ := by
    rw [← SchwartzMap.toLp_fourier_eq, Lp.norm_fourier_eq]
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h
  exact (ENNReal.toReal_eq_toReal_iff' ((𝓕 f : 𝓢(E, ℂ)).memLp 2 volume).eLpNorm_ne_top
    (f.memLp 2 volume).eLpNorm_ne_top).1 h
end GroundTheory.Automorphic.Sobolev
