-- Prove2me | solution 1 for OAI.MainGap.represented_mixed_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:41:36.365922+00:00
-- url     : https://prove2.me/submissions/56a441f0-5a59-43d1-9743-b211cd3dba29

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean:L251-L274
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.represented_mixed_estimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Defect ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.deficiencyOrder
attribute [local instance] OAI.MainGap.deficiencyStarOrder
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.scalingDefectOrder
attribute [local instance] OAI.MainGap.scalingDefectStarOrder
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourFixedOrder
attribute [local instance] OAI.MainGap.fourFixedStarOrder
end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
attribute [local instance] OAI.MainGap.defectSandwichOrder
attribute [local instance] OAI.MainGap.defectSandwichStarOrder
attribute [local instance] OAI.MainGap.representedDefectOrder
attribute [local instance] OAI.MainGap.representedDefectStarOrder
lemma firstSandwich_single_le {U V w : A} (hV : 0 ≤ V) (η : ℝ) {E : Finset A}
    (hw : w ∈ E) :
    (cut U η * w * CFC.sqrt V) * star (cut U η * w * CFC.sqrt V) ≤
      firstSandwich U V η E := by
  have hsum : w * V * star w ≤ ∑ v ∈ E, v * V * star v :=
    Finset.single_le_sum (fun v _ => star_right_conjugate_nonneg hV v) hw
  have h := conjugate_le_conjugate_of_nonneg hsum (cut_nonneg U η)
  have heq : (cut U η * w * CFC.sqrt V) * star (cut U η * w * CFC.sqrt V) =
      cut U η * (w * V * star w) * cut U η := by
    simp only [star_mul, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg V) |>.star_eq,
      IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq]
    calc
      _ = cut U η * w * (CFC.sqrt V * CFC.sqrt V) * star w * cut U η := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self V hV]; noncomm_ring
  rw [heq]
  exact h

lemma represented_single_sq_le (π : A →⋆ₐ[ℂ] D) {U V w : A} (hV : 0 ≤ V)
    (η : ℝ) {E : Finset A} (hw : w ∈ E) :
    ‖π (cut U η * w * CFC.sqrt V)‖ ^ 2 ≤ ‖π (firstSandwich U V η E)‖ := by
  have h := OrderHomClass.mono π (firstSandwich_single_le (U := U) hV η hw)
  rw [map_mul, map_star] at h
  simpa only [CStarRing.norm_self_mul_star, sq] using
    CStarAlgebra.norm_le_norm_of_le_of_nonneg h (mul_star_self_nonneg _)

lemma represented_mixed_estimate (π : A →⋆ₐ[ℂ] D) {U V w : A} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {η : ℝ} (hη : 0 < η) {E : Finset A} (hw : w ∈ E)
    (hD : ‖π (firstSandwich U V η E)‖ ≤ 2*η) :
    ‖π (U*w*V)‖ ≤ Real.sqrt (2*η) * ‖CFC.sqrt V‖ + η*‖w‖*‖V‖ := by
  have hr : ‖π (cut U η * w * CFC.sqrt V)‖ ≤ Real.sqrt (2*η) := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      ((represented_single_sq_le π hV η hw).trans hD)
  have hsplit : U*w*V = (cut U η * w * CFC.sqrt V) * CFC.sqrt V +
      (U-cut U η)*w*V := by
    rw [mul_assoc (cut U η * w), CFC.sqrt_mul_sqrt_self V hV]
    noncomm_ring
  rw [hsplit, map_add]
  apply norm_add_le _ _ |>.trans
  apply add_le_add
  · rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul hr (NonUnitalStarAlgHom.norm_apply_le π _) (norm_nonneg _) (by positivity))
  · rw [map_mul, map_mul]
    calc
      ‖(π (U-cut U η) * π w) * π V‖ ≤ ‖π (U-cut U η)‖ * ‖π w‖ * ‖π V‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ η*‖w‖*‖V‖ := mul_le_mul
        (mul_le_mul ((NonUnitalStarAlgHom.norm_apply_le π _).trans (norm_sub_cut_le hU hη.le))
          (NonUnitalStarAlgHom.norm_apply_le π w) (norm_nonneg _) hη.le)
        (NonUnitalStarAlgHom.norm_apply_le π V) (norm_nonneg _) (by positivity)

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.defectSandwichOrder
attribute [local instance] OAI.MainGap.defectSandwichStarOrder
attribute [local instance] OAI.MainGap.representedDefectOrder
attribute [local instance] OAI.MainGap.representedDefectStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.represented_mixed_estimate := @_root_.OAI.MainGap.represented_mixed_estimate
