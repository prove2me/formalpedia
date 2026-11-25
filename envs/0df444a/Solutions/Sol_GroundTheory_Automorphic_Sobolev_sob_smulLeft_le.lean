-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_smulLeft_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:43.184115+00:00
-- url     : https://prove2.me/submissions/cad76206-90f5-4cb8-be88-fcdb0c9b8e0f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_smulLeft_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_ofSchwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_le_of_schwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_coe
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulConst_nonneg

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
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r : ℝ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    sob r (smulLeftCLM ℂ (χ : E → ℂ) u) ≤ ENNReal.ofReal (mulConst r χ) * sob r u := by
  refine sob_le_of_schwartz _ (mulConst_nonneg r χ) (fun φ ↦ ?_) hu
  rw [smulLeftCLM_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (mulConst_nonneg r χ)]
  exact ENNReal.ofReal_le_ofReal (norm_ofSchwartz_smulLeft_le χ r φ)
end GroundTheory.Automorphic.Sobolev
