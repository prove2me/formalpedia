-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.abs_weight_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:59.691013+00:00
-- url     : https://prove2.me/submissions/d05643f8-c642-4a13-96e4-e405b8ab89e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasFDerivAt_one_add_norm_sq_rpow
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_fderiv_weight_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_peetre


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
theorem _root_.solution (r : ℝ) (ξ η : E) :
    |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| ≤
      |r| * 2 ^ (|r - 1| / 2) * ‖ξ - η‖ * (1 + ‖ξ - η‖ ^ 2) ^ (|r - 1| / 2) *
        (1 + ‖η‖ ^ 2) ^ ((r - 1) / 2) := by
  have hbound : ∀ ζ ∈ segment ℝ η ξ,
      ‖(r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)‖ ≤
        |r| * (2 ^ (|r - 1| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|r - 1| / 2) *
          (1 + ‖η‖ ^ 2) ^ ((r - 1) / 2)) := by
    intro ζ hζ
    refine (norm_fderiv_weight_le r ζ).trans ?_
    gcongr
    have hp := peetre ((r - 1) / 2) ζ η
    rw [abs_div, abs_two] at hp
    refine hp.trans ?_
    gcongr
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hζ
    have : a • η + b • ξ - η = b • (ξ - η) := by
      have ha' : a = 1 - b := by linarith
      rw [ha', sub_smul, one_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have : b ≤ 1 := by linarith
    calc b * ‖ξ - η‖ ≤ 1 * ‖ξ - η‖ := by gcongr
      _ = ‖ξ - η‖ := one_mul _
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (r / 2))
    (fun ζ _ ↦ (hasFDerivAt_one_add_norm_sq_rpow r ζ).hasFDerivWithinAt) hbound
    (convex_segment η ξ) (left_mem_segment ℝ η ξ) (right_mem_segment ℝ η ξ)
  rw [Real.norm_eq_abs] at h
  calc _ ≤ _ := h
    _ = _ := by ring
end GroundTheory.Automorphic.Sobolev
