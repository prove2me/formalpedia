-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:04:03.940063+00:00
-- url     : https://prove2.me/submissions/000b4e3f-4075-473e-b53e-df2b1c4dd0d0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1206-L1221
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_primal_filter_tail_le
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_span_coordinates_finite_support

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma sub_filterPrimal (p : ι → Prop) (u : T.Primal) :
    u - T.filterPrimal p u = T.filterPrimal (fun x => ¬ p x) u := by
  apply Finsupp.ext
  intro v
  change T.ofPrimal (u - T.filterPrimal p u) v =
    T.ofPrimal (T.filterPrimal (fun x => ¬ p x) u) v
  simp only [ofPrimal_sub, ofPrimal_filter, Finsupp.sub_apply, Finsupp.filter_apply]
  split_ifs <;> simp_all

lemma sum_units_eq_filter (H : Finset ι) (u : T.Primal) :
    (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) = T.filterPrimal (· ∈ H) u := by
  classical
  apply Finsupp.ext
  intro w
  change T.ofPrimal (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) w =
    T.ofPrimal (T.filterPrimal (· ∈ H) u) w
  simp only [ofPrimal_sum, ofPrimal_smul, ofPrimal_filter, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [ofPrimal, unitFinite, Finsupp.single_apply,
    mul_ite, Finset.sum_ite_eq']
  convert (Finsupp.filter_apply (· ∈ H) (T.ofPrimal u) w).symm using 1
  all_goals congr

lemma headPrimal_coe (H : Finset ι) (u : T.Primal) :
    T.headPrimal H (u : T.JamesSpace) =
      (T.filterPrimal (· ∈ H) u : T.JamesSpace) := by
  classical
  rw [headPrimal_apply, ← T.sum_units_eq_filter]
  simp only [coordinate_coe, unitVector]
  change (∑ v ∈ H, T.ofPrimal u v •
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (T.unitFinite v)) =
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v)
  simp only [map_sum, map_smul]

lemma tailDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.tailDual H x u = x (u - T.headPrimal H u) := by
  simp [tailDual_apply, mul_comm]

lemma headDual_eq_self {H : Finset ι} {x : T.Dual}
    (hx : ∀ v, v ∉ H → x (T.unitVector v) = 0) : T.headDual H x = x := by
  apply T.dual_ext
  intro v
  rw [headDual_unit]
  split_ifs with hv
  · rfl
  · exact (hx v hv).symm

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma tailPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖u - A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    rw [SegmentSystem.sub_filterPrimal, SegmentSystem.norm_eq_primal,
      SegmentSystem.norm_eq_primal, SegmentSystem.ofPrimal_filter]
    convert A.primal_filter_tail_le hH (A.segments.ofPrimal u) using 1
    congr 2

lemma tailDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.tailDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.tailDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.tailPrimal_norm_le hH u)
    (norm_nonneg _))

lemma coordinate_predual_approximation
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual} (hx : x ∈ A.segments.CoordinatePredual)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < ε := by
  have hxcl : x ∈ closure (Submodule.span ℝ (Set.range A.segments.coordinate) : Set A.segments.Dual) := hx
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hxcl ε hε
  obtain ⟨S,hS⟩ := A.segments.span_coordinates_finite_support hz
  obtain ⟨H,hSH,hH⟩ := hfin S
  have hPH : A.segments.headDual H z = z :=
    A.segments.headDual_eq_self (fun v hv => hS v (fun h => hv (hSH h)))
  refine ⟨H,hH,?_⟩
  have he : A.segments.tailDual H x = A.segments.tailDual H (x-z) := by
    simp only [map_sub, SegmentSystem.tailDual_apply, hPH, sub_self, sub_zero]
  rw [he]
  exact lt_of_le_of_lt (A.tailDual_norm_le hH (x-z)) (by simpa only [dist_eq_norm] using hclose)

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation := @_root_.OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation
