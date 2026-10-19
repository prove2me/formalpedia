-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.segment_filter_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:32:17.154665+00:00
-- url     : https://prove2.me/submissions/c3e2f53d-deb6-4722-adeb-e1d2fec2f657

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L81-L103
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.segment_filter_tail. The node keeps its source
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
lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma segment_filter_tail {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∉ H)).Nonempty → A.segments.IsSegment (S.filter (· ∉ H)) := by
  classical
  intro hne
  obtain ⟨c, hc, hmin⟩ := Finset.exists_minimal hne
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcH : c ∉ H := (Finset.mem_filter.mp hc).2
  have hleast : ∀ v ∈ S.filter (· ∉ H), c ≤ v := by
    intro v hv
    rcases A.interval_chain hS c hcS v (Finset.mem_filter.mp hv).1 with h | h
    · exact h
    · exact hmin hv h
  obtain ⟨a, b, hab, hmem⟩ := hS
  refine ⟨c, b, ((hmem c).mp hcS).2, ?_⟩
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨hleast v (Finset.mem_filter.mpr hv), ((hmem v).mp hv.1).2⟩
  · intro hv
    refine ⟨(hmem v).mpr ⟨((hmem c).mp hcS).1.trans hv.1, hv.2⟩, ?_⟩
    exact fun hvH => hcH (hH hv.1 hvH)

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.segment_filter_tail := @_root_.OAI.DiamondDistortion.Ancestry.segment_filter_tail
