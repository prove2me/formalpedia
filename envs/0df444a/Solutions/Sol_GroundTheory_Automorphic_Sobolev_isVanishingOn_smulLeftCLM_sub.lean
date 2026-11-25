-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:03:33.315974+00:00
-- url     : https://prove2.me/submissions/744baa08-793b-40cd-8247-6f4283938f0a

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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth) {V : Set E}
    (hgV : ∀ x ∈ V, g x = 1) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u - u) V := by
  intro φ hφ
  rw [sub_apply, smulLeftCLM_apply_apply, sub_eq_zero]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  by_cases hx : φ x = 0
  · rw [hx, mul_zero]
  · rw [hgV x (hφ (subset_tsupport φ hx)), one_mul]
end GroundTheory.Automorphic.Sobolev
