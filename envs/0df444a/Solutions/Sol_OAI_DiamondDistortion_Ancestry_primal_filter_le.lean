-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.primal_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:48:27.135118+00:00
-- url     : https://prove2.me/submissions/c232f895-7cca-485e-9b44-74685113d830

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L648-L669
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.primal_filter_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_head
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_test_energy_le_allow_empty

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
lemma primal_filter_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∈ H)) ≤ A.segments.primalSeminorm u := by
  classical
  rw [SegmentSystem.primalSeminorm,
    Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  have h := A.segments.test_energy_le_allow_empty
    (fun i => (F.seg i).filter (· ∈ H))
    (fun i hne => A.segment_filter_head (F.allowed i) hH hne)
    (fun i j hij => (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)) u
  have he : ‖F.test (u.filter (· ∈ H))‖ ^ 2 =
      ∑ i, (∑ v ∈ (F.seg i).filter (· ∈ H), u v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [SegmentSystem.Family.test, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    congr 1
    simp [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp h

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.primal_filter_le := @_root_.OAI.DiamondDistortion.Ancestry.primal_filter_le
