-- Prove2me | solution 1 for Mycielski.card_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:00.701864+00:00
-- url     : https://prove2.me/submissions/f5d07ca4-07c1-41c5-95bd-f5f3d4f20209

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
theorem _root_.solution {V : Type u} [Fintype V] :
    Fintype.card (Vertex V) = 2 * Fintype.card V + 1 := by
  simp only [Vertex, Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  omega
end Mycielski
