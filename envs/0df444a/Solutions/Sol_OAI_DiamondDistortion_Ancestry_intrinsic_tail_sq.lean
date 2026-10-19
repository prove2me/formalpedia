-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:01:03.946771+00:00
-- url     : https://prove2.me/submissions/88996725-a502-4995-9dc6-5f2475da01c8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1139-L1188
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_intrinsic_tail_test
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_primal_filter_le

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

lemma headDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.headDual H x u = x (T.headPrimal H u) := by
  simp [headDual_apply, headPrimal_apply, mul_comm]

lemma headDual_eq_self {H : Finset ι} {x : T.Dual}
    (hx : ∀ v, v ∉ H → x (T.unitVector v) = 0) : T.headDual H x = x := by
  apply T.dual_ext
  intro v
  rw [headDual_unit]
  split_ifs with hv
  · rfl
  · exact (hx v hv).symm

lemma headArray_outside (H : Finset ι) (u : T.JamesSpace) {v : ι} (hv : v ∉ H) :
    T.headArray H u v = 0 := by
  classical
  simp [headArray, Finsupp.finsetSum_apply, Finsupp.single_apply, hv,
    Finset.sum_ite_eq']

lemma finiteEmbedding_headArray (H : Finset ι) (u : T.JamesSpace) :
    T.finiteEmbedding (T.headArray H u) = T.headPrimal H u := by
  simp only [headArray, map_sum, map_smul, finiteEmbedding_single, one_smul,
    headPrimal_apply]

variable {T}

variable (T)

lemma finiteEmbedding_norm (p : ι →₀ ℝ) :
    ‖T.finiteEmbedding p‖ = T.primalSeminorm p := by
  rw [finiteEmbedding_apply, UniformSpace.Completion.norm_coe]
  rfl

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
lemma headPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact A.primal_filter_le hH u

lemma norm_center_le {x y : A.segments.Dual} {R : ℝ}
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := (norm_add_le (x+y) (x-y)).trans (add_le_add hplus hminus)
  have he : (x+y)+(x-y) = (2:ℝ) • x := by module
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  linarith

lemma intrinsic_tail_sq
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 ≤ R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) :
    ‖A.segments.tailDual H y‖^2 + 4*‖x‖^2 ≤ 4*R^2 := by
  have hxr := A.norm_center_le hplus hminus
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hxr) (norm_nonneg _))
    have hy0 : y=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0,hx0] using hplus) (norm_nonneg _))
    simp [hx0,hy0,← hR0]
  let t := ‖A.segments.tailDual H y‖
  have ht : 0 ≤ t := norm_nonneg _
  have htn : t ≤ 2*R := by
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus 0 (by simp) (by simp)
    simpa only [map_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hR] using h
  have ht2 : t^2 ≤ (2*R)^2 := (sq_le_sq₀ ht (by positivity)).2 htn
  have hrad : 0 ≤ R^2-t^2/4 := by nlinarith
  have hxn : ‖x‖ ≤ Real.sqrt (R^2-t^2/4) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro u hu
    let p := A.segments.headArray H u
    have hp : ∀ v, v ∉ H → p v=0 := fun v hv => A.segments.headArray_outside H u hv
    have hpn : A.segments.primalSeminorm p ≤ 1 := by
      rw [← SegmentSystem.finiteEmbedding_norm, SegmentSystem.finiteEmbedding_headArray]
      exact (A.headPrimal_norm_le hH u).trans hu.le
    have he : x (A.segments.finiteEmbedding p) = x u := by
      rw [SegmentSystem.finiteEmbedding_headArray, ← SegmentSystem.headDual_apply_apply,
        A.segments.headDual_eq_self hx]
    have hval : |x u| ≤ R := by
      have h := x.le_opNorm u
      rw [Real.norm_eq_abs, hu, mul_one] at h
      exact h.trans hxr
    have hval2 : (x u)^2 ≤ R^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hval
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus p hp hpn
    rw [he] at h
    have hsq : t^2 ≤ (2*Real.sqrt (R^2-(x u)^2))^2 :=
      (sq_le_sq₀ ht (by positivity)).2 h
    have hs := Real.sq_sqrt (sub_nonneg.mpr hval2)
    have hv2 : (x u)^2 ≤ R^2-t^2/4 := by nlinarith
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hrad]
    exact hv2
  have hxn2 := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).2 hxn
  rw [Real.sq_sqrt hrad] at hxn2
  change t^2+4*‖x‖^2 ≤ 4*R^2
  nlinarith

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq := @_root_.OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq
