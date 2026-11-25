-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:04:57.61825+00:00
-- url     : https://prove2.me/submissions/2bcd6bea-ca48-4aa4-b78a-54de6ac9dbf1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u) (tsupport g)ᶜ := by
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  have : SchwartzMap.smulLeftCLM ℂ g φ = 0 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, zero_apply]
    by_cases hx : x ∈ tsupport g
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hφ h hx), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [this, map_zero]
end GroundTheory.Automorphic.Sobolev
