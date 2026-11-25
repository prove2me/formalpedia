-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:05.617806+00:00
-- url     : https://prove2.me/submissions/4a840326-b116-4611-bdee-a5a8d72b2b5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_not_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_inclusion_apply_le


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
theorem _root_.solution {s t : ℝ} (h : t ≤ s) (u : 𝓢'(E, ℂ)) : sob t u ≤ sob s u := by
  by_cases hu : MemSobolev s 2 u
  · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
    calc sob t (SobolevSpace.toDistribution u')
        = sob t (SobolevSpace.toDistribution (SobolevSpace.inclusion h u')) := by
          rw [SobolevSpace.toDistribution_inclusion]
      _ = ‖SobolevSpace.inclusion h u'‖ₑ := sob_toDistribution _
      _ ≤ ‖u'‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_inclusion_apply_le h u')
      _ = sob s (SobolevSpace.toDistribution u') := (sob_toDistribution _).symm
  · rw [sob_of_not_mem hu]; exact le_top
end GroundTheory.Automorphic.Sobolev
