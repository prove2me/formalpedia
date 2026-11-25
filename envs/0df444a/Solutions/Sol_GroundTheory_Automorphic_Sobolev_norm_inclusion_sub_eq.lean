-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_inclusion_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:06.282337+00:00
-- url     : https://prove2.me/submissions/3345fdec-3fbf-4a21-823d-b4ca49c00307

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich

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
theorem _root_.solution {s r : ℝ} (h : r ≤ s) (v w : SobolevSpace E ℂ s) :
    ‖SobolevSpace.inclusion h v - SobolevSpace.inclusion h w‖ =
      ‖(𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h v)) : Lp ℂ 2 (volume : Measure E)) -
        𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h w))‖ := by
  rw [SobolevSpace.norm_def, map_sub, ← Lp.norm_fourier_eq]
  congr 1
  exact (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _
end GroundTheory.Automorphic.Sobolev
