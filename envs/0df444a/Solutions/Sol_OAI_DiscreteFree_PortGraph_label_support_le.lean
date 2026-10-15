-- Prove2me | solution 1 for OAI.DiscreteFree.PortGraph.label_support_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:22:14.160266+00:00
-- url     : https://prove2.me/submissions/b555bd8d-200c-4b0c-b321-3a670a8b7984

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/PortGraphs.lean:L175-L191
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.PortGraph.label_support_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs

-- ---- from OAI.Analysis.LipschitzFree.PortGraphs ----
namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

theorem label_witness {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X)
    (h : G.label color cap i x < cap) :
    ∃ w : List D, w.length = G.label color cap i x ∧ color (G.walk x w) = i := by
  have hh := Nat.find_spec (show ∃ n : ℕ, n = cap ∨ ∃ w : List D,
    w.length = n ∧ color (G.walk x w) = i from ⟨cap, Or.inl rfl⟩)
  exact hh.resolve_left (Nat.ne_of_lt h)

end PortGraph

namespace BoundedWords
variable {D : Type*}

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

theorem label_support_le {C : Type*} [Fintype C] (color : X → C) (cap : ℕ)
    (x : X) : Nat.card {i : C // G.label color cap i x < cap} ≤
      Fintype.card (BoundedWords D cap) := by
  classical
  let f : {i : C // G.label color cap i x < cap} → BoundedWords D cap := fun i =>
    let w := (G.label_witness color cap i.val x i.property).choose
    ⟨w, by
      rw [(G.label_witness color cap i.val x i.property).choose_spec.1]
      exact G.label_le color cap i.val x⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hi := (G.label_witness color cap i.val x i.property).choose_spec.2
    have hj := (G.label_witness color cap j.val x j.property).choose_spec.2
    have he := congrArg (fun w : BoundedWords D cap => color (G.walk x w.val)) hij
    exact hi.symm.trans (he.trans hj)
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.PortGraph
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.PortGraph.label_support_le := @_root_.OAI.DiscreteFree.PortGraph.label_support_le
