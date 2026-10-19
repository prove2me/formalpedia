-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:29:31.335482+00:00
-- url     : https://prove2.me/submissions/59f600b7-de31-4bdd-bb1b-6249e0c25b51

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L1088-L1110
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

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

variable {T}

variable (T)

lemma span_coordinates_finite_support {x : T.Dual}
    (hx : x ∈ Submodule.span ℝ (Set.range T.coordinate)) :
    ∃ S : Finset ι, ∀ v, v ∉ S → x (T.unitVector v)=0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    refine ⟨{v}, ?_⟩
    intro w hw
    simp only [Finset.mem_singleton] at hw
    simp [coordinate_unitVector,hw]
  | zero => exact ⟨∅, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨S,hS⟩ := hx
    obtain ⟨U,hU⟩ := hy
    refine ⟨S ∪ U, ?_⟩
    intro v hv
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
    have hvU : v ∉ U := fun h => hv (Finset.mem_union_right _ h)
    simp only [add_apply,hS v hvS,hU v hvU,add_zero]
  | smul a x _ hx =>
    obtain ⟨S,hS⟩ := hx
    exact ⟨S, fun v hv => by simp only [smul_apply,hS v hv,smul_zero]⟩

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support := @_root_.OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support
