-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.primal_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:12:16.581817+00:00
-- url     : https://prove2.me/submissions/08803de3-accc-4e05-8cac-50b4ac347c34

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean:L20-L34
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.primal_sq_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality

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

lemma primal_sq_le (p : ι →₀ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : T.Family, (∑ i, (∑ v ∈ F.seg i,p v)^2) ≤ M) :
    (T.primalSeminorm p)^2 ≤ M := by
  have hbound : T.primalSeminorm p ≤ Real.sqrt M := by
    rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
    apply ciSup_le
    intro F
    have h := hF F
    have he : ‖F.test p‖^2 = (∑ i, (∑ v ∈ F.seg i,p v)^2) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Family.test_apply,Real.norm_eq_abs,sq_abs]
    rw [← he, ← Real.sq_sqrt hM] at h
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  have h := (sq_le_sq₀ (apply_nonneg _ _) (Real.sqrt_nonneg _)).2 hbound
  rwa [Real.sq_sqrt hM] at h

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.primal_sq_le := @_root_.OAI.DiamondDistortion.SegmentSystem.primal_sq_le
