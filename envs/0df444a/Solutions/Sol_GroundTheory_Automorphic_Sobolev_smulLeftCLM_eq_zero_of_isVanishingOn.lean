-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_zero_of_isVanishingOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:46.290632+00:00
-- url     : https://prove2.me/submissions/c3802726-867c-4824-95a2-64099e351537

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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) (hgU : tsupport g ⊆ U) :
    smulLeftCLM ℂ g u = 0 := by
  ext φ
  rw [smulLeftCLM_apply_apply, zero_apply]
  apply hu
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_left g φ).trans hgU
end GroundTheory.Automorphic.Sobolev
