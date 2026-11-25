-- Prove2me | solution 1 for Mycielski.cliqueFree_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:58.4329+00:00
-- url     : https://prove2.me/submissions/4d1d020a-904f-4eea-adde-351819af7e6e

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Mycielski_Basic
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_original
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_cliqueFree_three_iff
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_original
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.apex_adj_shadow

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u
namespace Mycielski
theorem _root_.solution {V : Type u} {G : SimpleGraph V} (h : G.CliqueFree 3) :
    (graph G).CliqueFree 3 := by
  rw [cliqueFree_three_iff] at h ⊢
  rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) (_ | ⟨z, bz⟩) <;>
    (try cases bv) <;> (try cases bw) <;> (try cases bz) <;>
    simp only [graph, Adj] <;> aesop
end Mycielski
