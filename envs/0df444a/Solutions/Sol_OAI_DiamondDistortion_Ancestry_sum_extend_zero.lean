-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.sum_extend_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:38:04.620327+00:00
-- url     : https://prove2.me/submissions/2b526316-e5b9-41e2-b85f-81ba04c62454

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L259-L273
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.sum_extend_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

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
/-- Zero-extension along a finite injection preserves the finite sum. -/
lemma sum_extend_zero {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ↪ ν) (f : κ → ℝ) :
    (∑ i, Function.extend e f (fun _ => 0) i) = ∑ a, f a := by
  classical
  let I := Finset.univ.image e
  have hz : ∀ i ∈ Finset.univ, i ∉ I → Function.extend e f (fun _ => 0) i = 0 := by
    intro i _ hi
    apply Function.extend_apply'
    simpa [I] using hi
  rw [← Finset.sum_subset (Finset.subset_univ I) hz,
    Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  exact e.injective.extend_apply _ _ _

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.sum_extend_zero := @_root_.OAI.DiamondDistortion.Ancestry.sum_extend_zero
