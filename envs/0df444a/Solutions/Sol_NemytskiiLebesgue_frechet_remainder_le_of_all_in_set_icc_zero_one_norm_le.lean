-- Prove2me | solution 1 for NemytskiiLebesgue.frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:11.703961+00:00
-- url     : https://prove2.me/submissions/b6b6f447-c02a-4335-b467-f0a8bf141d03

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {g' : E → E →L[ℝ] F} (hgg' : ∀ ξ : E, HasFDerivAt g (g' ξ) ξ)
    {x e : E} {M : ℝ} (hxeM : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖g' (x + t • e) - g' x‖ ≤ M) :
    ‖g (x + e) - g x - g' x e‖ ≤ M * ‖e‖ := by
  have remainder : ∀ ξ ∈ segment ℝ x (x + e), ‖g' ξ - g' x‖ ≤ M := by
    simp_all only [Set.mem_Icc,
        and_imp,
        segment_eq_image,
        smul_add,
        Set.mem_image,
        forall_exists_index]
    rintro _ t ht₁ ht₂ rfl
    convert hxeM t ht₁ ht₂ using 1
    simp [←add_assoc, ←add_smul]
  convert (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (show ∀ ξ ∈ segment ℝ x (x + e), HasFDerivWithinAt (fun ξ : E => g ξ - g' x ξ)
        (g' ξ - g' x) (segment ℝ x (x + e)) ξ from
        fun ξ : E => ↓(HasFDerivAt.hasFDerivWithinAt
          (HasFDerivAt.sub (hgg' ξ) (ContinuousLinearMap.hasFDerivAt _))))
      remainder (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)
    ) using 1 <;> simp [sub_sub_sub_comm]
end NemytskiiLebesgue
