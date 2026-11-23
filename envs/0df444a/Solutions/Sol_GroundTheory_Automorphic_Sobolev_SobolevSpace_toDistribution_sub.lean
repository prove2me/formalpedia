-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.044001+00:00
-- url     : https://prove2.me/submissions/436b9704-ff36-4514-8601-d40a98c87f4a

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
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (u v : SobolevSpace E F s) :
    toDistribution (u - v) = toDistribution u - toDistribution v := rfl
end GroundTheory.Automorphic.Sobolev.SobolevSpace
