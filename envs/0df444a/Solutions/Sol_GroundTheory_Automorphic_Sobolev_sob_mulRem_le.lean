-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_mulRem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:19.850779+00:00
-- url     : https://prove2.me/submissions/c57e72ed-c4aa-4ee2-8ebc-7c99c338e388

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_wInt_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_commConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_commRem_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_ofSchwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_le_of_schwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulRem_coe

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
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r a : ℝ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev (r + a - 1) 2 u) :
    sob (r + a) (mulRem χ r u) ≤
      ENNReal.ofReal (commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ)) *
        sob (r + a - 1) u := by
  have hC := mul_nonneg (commConst_nonneg r a) (wInt_nonneg ((|a| + |r - 1| + 1) / 2) (𝓕 χ))
  refine sob_le_of_schwartz _ hC (fun φ ↦ ?_) hu
  rw [mulRem_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (norm_ofSchwartz_commRem_le χ r a φ)
end GroundTheory.Automorphic.Sobolev
