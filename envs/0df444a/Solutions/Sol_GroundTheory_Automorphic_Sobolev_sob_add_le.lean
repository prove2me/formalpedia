-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:33:59.643586+00:00
-- url     : https://prove2.me/submissions/8b420208-54df-4ba3-8268-885ccd43bdf2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_not_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff


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
theorem _root_.solution {s : ℝ} (u v : 𝓢'(E, ℂ)) : sob s (u + v) ≤ sob s u + sob s v := by
  by_cases hu : MemSobolev s 2 u
  · by_cases hv : MemSobolev s 2 v
    · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
      obtain ⟨v', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) v).2 hv
      rw [← SobolevSpace.toDistribution_add, sob_toDistribution, sob_toDistribution,
        sob_toDistribution]
      exact enorm_add_le _ _
    · rw [sob_of_not_mem hv, add_top]; exact le_top
  · rw [sob_of_not_mem hu, top_add]; exact le_top
end GroundTheory.Automorphic.Sobolev
