-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:17:16.14777+00:00
-- url     : https://prove2.me/submissions/7c4b13cb-f8b5-4026-811d-1436e4a6ce8c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean:L174-L188
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_primal_sq_le

-- ---- from OAI.Analysis.DiamondDistortion.Orthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

/-- No nonzero coordinate is lost by using the actual Finsupp support. -/
lemma sum_sq_le_support (p : ι →₀ ℝ) (S : Finset ι) :
    (∑ v ∈ S,p v^2) ≤ ∑ v ∈ p.support,p v^2 := by
  classical
  have h : (∑ v ∈ S,p v^2) ≤ ∑ v ∈ S ∪ p.support,p v^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => sq_nonneg _)
  have he : (∑ v ∈ p.support,p v^2) = ∑ v ∈ S ∪ p.support,p v^2 := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv
    rw [Finsupp.notMem_support_iff.mp hv]
    norm_num
  exact h.trans_eq he.symm

lemma primal_sq_le_of_segment (p : ι →₀ ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ S, T.IsSegment S → (∑ v ∈ S,p v)^2 ≤ L*(∑ v ∈ S,p v^2)) :
    (T.primalSeminorm p)^2 ≤ L*(∑ v ∈ p.support,p v^2) := by
  classical
  apply T.primal_sq_le p (mul_nonneg hL (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  intro F
  have he : (∑ i,∑ v ∈ F.seg i,p v^2) = ∑ v ∈ Finset.univ.biUnion F.seg,p v^2 := by
    symm
    apply Finset.sum_biUnion
    intro i _ j _ hij
    exact F.disjoint hij
  calc
    _ ≤ ∑ i,L*(∑ v ∈ F.seg i,p v^2) := Finset.sum_le_sum (fun i _ => hS _ (F.allowed i))
    _ = L*(∑ v ∈ Finset.univ.biUnion F.seg,p v^2) := by rw [← Finset.mul_sum,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_le_support p _) hL

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment := @_root_.OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment
