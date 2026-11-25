-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_fourierMultiplier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:34:01.537875+00:00
-- url     : https://prove2.me/submissions/32c3af0f-8c0b-48f2-9cbb-bc1b689d4364

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_multiplier_apply_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bound_nonneg


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
theorem _root_.solution {m : E → ℂ} (hm : m.HasTemperateGrowth) {C s t : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob t (fourierMultiplierCLM ℂ m u) ≤ ENNReal.ofReal C * sob s u := by
  obtain ⟨v, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
  rw [← SobolevSpace.toDistribution_multiplier hm hC, sob_toDistribution, sob_toDistribution,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (bound_nonneg hC)]
  exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_multiplier_apply_le hm hC v)
end GroundTheory.Automorphic.Sobolev
