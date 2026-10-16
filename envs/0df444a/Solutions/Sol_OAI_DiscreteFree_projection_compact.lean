-- Prove2me | solution 1 for OAI.DiscreteFree.projection_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:35:35.880158+00:00
-- url     : https://prove2.me/submissions/4c574c32-7811-49b2-ae5e-94e0c4de0ec1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/CompactApproximation.lean:L94-L117
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.projection_compact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Theorems.Thm_OAI_DiscreteFree_supportProjection_bound

-- ---- from OAI.Analysis.LipschitzFree.Coordinates ----
namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

namespace Lip0
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

omit [MetricSpace M] in
theorem sum_point_test {V : Type*} [AddCommMonoid V] (F : Finset M) (x : M) (v : M → V) :
    (∑ j ∈ F, if x = j ∧ j ≠ o then v j else 0) = if x ∈ F ∧ x ≠ o then v x else 0 := by
  have ht (j : M) : (if x = j ∧ j ≠ o then v j else 0) =
      if j = x then (if x ≠ o then v x else 0) else 0 := by
    by_cases h : j = x
    · subst j; simp
    · simp [h, Ne.symm h]
  simp_rw [ht]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem supportProjection_delta (F : Finset M) (x : M) :
    supportProjection o sep F (delta o x) = if x ∈ F then delta o x else 0 := by
  rw [supportProjection_apply]
  by_cases hx : x = o
  · subst x
    simp
  · simp only [coordinate_delta, ite_smul, one_smul, zero_smul]
    rw [sum_point_test]
    simp [hx]

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.CompactApproximation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Compact-uniform approximation on bounded separated spaces
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem evaluation_span_dense : Dense (Submodule.span ℝ (Set.range (delta o)) : Set (FreeSpace o)) := by
  let S := Submodule.span ℝ (Set.range (delta o))
  have hu : ∀ u : FreeSpace o, u ∈ S.topologicalClosure :=
    freeSpace_induction (fun u => u ∈ S.topologicalClosure)
      (Submodule.isClosed_topologicalClosure S) S.topologicalClosure.zero_mem
      (fun _ _ => S.topologicalClosure.add_mem)
      (fun c _ h => S.topologicalClosure.smul_mem c h)
      (fun x => Submodule.le_topologicalClosure S (Submodule.subset_span ⟨x, rfl⟩))
  intro u
  exact hu u

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem span_eventually_fixed {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ (Set.range (delta o))) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → supportProjection o sep G u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, rfl⟩ := h
    refine ⟨{x}, fun G hG => ?_⟩
    rw [supportProjection_delta, ite_eq_left (hG (Finset.mem_singleton_self _))]
  | zero => exact ⟨∅, fun _ _ => map_zero _⟩
  | add u v hu hv ihu ihv =>
    obtain ⟨F, hF⟩ := ihu
    obtain ⟨G, hG⟩ := ihv
    refine ⟨F ∪ G, fun K hK => ?_⟩
    rw [map_add, hF K (Finset.Subset.trans Finset.subset_union_left hK),
      hG K (Finset.Subset.trans Finset.subset_union_right hK)]
  | smul c u hu ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨F, fun G hG => by rw [map_smul, hF G hG]⟩

variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

include hB hb in
theorem projection_error_bound (F : Finset M) (u : FreeSpace o) :
    ‖supportProjection o sep F u - u‖ ≤ (2*B+1)*‖u‖ := by
  calc
    _ ≤ ‖supportProjection o sep F u‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ (2*B)*‖u‖ + ‖u‖ := add_le_add
      ((supportProjection o sep F).le_opNorm u |>.trans
        (mul_le_mul_of_nonneg_right (supportProjection_bound o sep F B hB hb) (norm_nonneg u))) le_rfl
    _ = _ := by ring

include hB hb in

theorem projection_pointwise (u : FreeSpace o) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp (evaluation_span_dense o u) _ (div_pos hε hK)
  obtain ⟨F, hF⟩ := span_eventually_fixed o sep hv
  refine ⟨F, fun G hG => ?_⟩
  calc
    ‖supportProjection o sep G u - u‖ =
        ‖supportProjection o sep G (u-v) - (u-v)‖ := by rw [map_sub, hF G hG]; congr 1; abel
    _ ≤ (2*B+1)*‖u-v‖ := projection_error_bound o sep B hB hb G (u-v)
    _ < ε := by
      rw [dist_eq_norm] at huv
      exact (lt_div_iff₀' hK).mp huv

include hB hb in

theorem projection_compact (C : Set (FreeSpace o)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ∀ u ∈ C,
      ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨t, _, ht, hcover⟩ := hC.finite_cover_balls (e := ε/(2*(2*B+1))) (by positivity)
  choose F hF using (fun z : FreeSpace o => projection_pointwise o sep B hB hb z (ε/2) (by positivity))
  refine ⟨ht.toFinset.biUnion F, fun G hG u hu => ?_⟩
  obtain ⟨z, hz, huz⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hzF : F z ⊆ G := (Finset.subset_biUnion_of_mem F (ht.mem_toFinset.mpr hz)).trans hG
  have hze := hF z G hzF
  have huz' : ‖u-z‖ < ε/(2*(2*B+1)) := by simpa only [Metric.mem_ball, dist_eq_norm] using huz
  have hsmall : (2*B+1)*‖u-z‖ < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(2*B+1))).mp huz'
    nlinarith
  calc
    ‖supportProjection o sep G u - u‖ =
      ‖(supportProjection o sep G (u-z) - (u-z)) + (supportProjection o sep G z - z)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖supportProjection o sep G (u-z) - (u-z)‖ + ‖supportProjection o sep G z - z‖ := norm_add_le _ _
    _ ≤ (2*B+1)*‖u-z‖ + ‖supportProjection o sep G z - z‖ :=
      add_le_add (projection_error_bound o sep B hB hb G (u-z)) le_rfl
    _ < ε := by linarith

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.projection_compact := @_root_.OAI.DiscreteFree.projection_compact
