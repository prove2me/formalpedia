-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:02:42.077136+00:00
-- url     : https://prove2.me/submissions/6246e956-e509-4470-a80a-8fac14fb6b0c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1190-L1204
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors. The node keeps its source
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
lemma finite_heads_of_predecessors
    (hpred : ∀ b : ι, ({a : ι | a ≤ b} : Set ι).Finite) :
    ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι) := by
  classical
  intro S
  let U : Set ι := ⋃ b ∈ (S : Set ι), {a : ι | a ≤ b}
  have hU : U.Finite := S.finite_toSet.biUnion (fun b _ => hpred b)
  refine ⟨hU.toFinset, ?_, ?_⟩
  · intro b hb
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, le_rfl⟩⟩
  · intro a b hab hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hb ⊢
    obtain ⟨c,hc,hbc⟩ := Set.mem_iUnion₂.mp hb
    exact Set.mem_iUnion₂.mpr ⟨c,hc,hab.trans hbc⟩

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors := @_root_.OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors
