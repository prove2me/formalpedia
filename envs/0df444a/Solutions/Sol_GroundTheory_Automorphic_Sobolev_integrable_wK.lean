-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.integrable_wK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:02.238257+00:00
-- url     : https://prove2.me/submissions/4118ed00-319d-4249-884d-d5d61cca45ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_continuous_one_add_norm_sq_rpow
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_norm_le_weight


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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (c : ℝ) (ψ : 𝓢(E, ℂ)) :
    Integrable (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖) (volume : Measure E) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_norm_le_weight ψ (-(n + 1) - 2 * c)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := n + 1) (by linarith)).const_mul C
  refine hint.mono' ((continuous_one_add_norm_sq_rpow c).mul ψ.continuous.norm).aestronglyMeasurable
    (ae_of_all _ fun ζ ↦ ?_)
  have pζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖ ≤ (1 + ‖ζ‖ ^ 2) ^ c * (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) - 2 * c) / 2)) := by
        gcongr; exact hC ζ
    _ = C * (1 + ‖ζ‖ ^ 2) ^ (-(n + 1) / 2) := by
        rw [mul_left_comm, ← Real.rpow_add pζ]; congr 2; ring
end GroundTheory.Automorphic.Sobolev
