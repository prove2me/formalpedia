-- Prove2me | solution 2 for OAI.DiamondDistortion.Ancestry.finite_head_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:08:07.168335+00:00
-- url     : https://prove2.me/submissions/9c5db579-7c2b-482f-8917-cf0b477346c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1223-L1252
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.finite_head_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
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
lemma headPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact A.primal_filter_le hH u

lemma headDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.headDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.headDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.headPrimal_norm_le hH u)
    (norm_nonneg _))

/-- Finite-dimensional compactness compares distinct members of any bounded
    sequence; no maximum over the infinitely many children is asserted. -/
lemma finite_head_pair {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (z : ℕ → A.segments.Dual) {R η : ℝ} (hz : ∀ i, ‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖A.segments.headDual H ((1/2:ℝ) • (z i-z j))‖ < η := by
  classical
  let M := Submodule.span ℝ (A.segments.coordinate '' (H : Set ι))
  have : FiniteDimensional ℝ M :=
    FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image A.segments.coordinate)
  have hm (w : A.segments.Dual) : A.segments.headDual H w ∈ M := by
    rw [SegmentSystem.headDual_apply]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem M _ (Submodule.subset_span ⟨v,hv,rfl⟩)
  let Z : ℕ → M := fun i => ⟨A.segments.headDual H (z i),hm (z i)⟩
  have hZ (i : ℕ) : Z i ∈ Metric.closedBall (0 : M) R := by
    rw [Metric.mem_closedBall]
    change dist (A.segments.headDual H (z i)) 0 ≤ R
    rw [dist_zero_right]
    exact (A.headDual_norm_le hH (z i)).trans (hz i)
  obtain ⟨a,_,φ,hφ,hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hZ
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (2*η) (by positivity)
  have hd := hN N le_rfl (N+1) (by omega)
  change dist (Z (φ N)) (Z (φ (N+1))) < 2*η at hd
  change dist (A.segments.headDual H (z (φ N))) (A.segments.headDual H (z (φ (N+1)))) < 2*η at hd
  rw [dist_eq_norm] at hd
  change ‖A.segments.headDual H (z (φ N)) - A.segments.headDual H (z (φ (N+1)))‖ < 2*η at hd
  refine ⟨φ N, φ (N+1), hφ.injective.ne (by omega), ?_⟩
  rw [map_smul,norm_smul,map_sub,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.finite_head_pair := @_root_.OAI.DiamondDistortion.Ancestry.finite_head_pair
