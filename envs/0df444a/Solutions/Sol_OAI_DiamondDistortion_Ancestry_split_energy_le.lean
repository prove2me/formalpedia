-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.split_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:33:45.140329+00:00
-- url     : https://prove2.me/submissions/b9ca9b9e-76b6-4f4d-9561-d7cc5942c900

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L105-L142
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.split_energy_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_head
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_tail
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
/-- Splitting each member of a disjoint family at its own ancestral cut preserves
    the testing budget. This is the simultaneous, not one-gate-at-a-time, estimate. -/
lemma split_energy_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, ((∑ v ∈ (F.seg i).filter (· ∈ H i), u v) ^ 2 +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2)) ≤
      (A.segments.primalSeminorm u) ^ 2 := by
  classical
  let P : Fin F.n × Bool → Finset ι := fun z =>
    if z.2 then (F.seg z.1).filter (· ∉ H z.1) else (F.seg z.1).filter (· ∈ H z.1)
  have hp : ∀ z, (P z).Nonempty → A.segments.IsSegment (P z) := by
    rintro ⟨i, b⟩
    cases b
    · exact A.segment_filter_head (F.allowed i) (hH i)
    · exact A.segment_filter_tail (F.allowed i) (hH i)
  have hs : ∀ z, P z ⊆ F.seg z.1 := by
    rintro ⟨i, b⟩
    cases b <;> exact Finset.filter_subset _ _
  have hd : Pairwise (fun z w => Disjoint (P z) (P w)) := by
    intro z w hzw
    by_cases h : z.1 = w.1
    · obtain ⟨i, b⟩ := z
      obtain ⟨j, c⟩ := w
      dsimp at h
      subst j
      apply Finset.disjoint_left.mpr
      intro v hv hw
      cases b <;> cases c
      · exact hzw rfl
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hw.2 hv.2
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hv.2 hw.2
      · exact hzw rfl
    · exact (F.disjoint h).mono (hs z) (hs w)
  have he := A.segments.test_energy_le_allow_empty P hp hd u
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte,
    add_comm] using he

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.split_energy_le := @_root_.OAI.DiamondDistortion.Ancestry.split_energy_le
