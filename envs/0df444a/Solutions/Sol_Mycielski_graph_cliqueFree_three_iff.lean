-- Prove2me | solution 1 for Mycielski.graph_cliqueFree_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:39.987525+00:00
-- url     : https://prove2.me/submissions/57df303c-891d-4b21-b99e-4de543248d65

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Mycielski_Basic
public import Theorems.Thm_Mycielski_cliqueFree_three_iff
public import Theorems.Thm_Mycielski_cliqueFree_three

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u
namespace Mycielski
theorem _root_.solution {V : Type u} (G : SimpleGraph V) :
    (graph G).CliqueFree 3 ↔ G.CliqueFree 3 := by
  constructor
  · intro h
    rw [cliqueFree_three_iff] at h ⊢
    intro v w z hvw hvz hwz
    exact h (original v) (original w) (original z) hvw hvz hwz
  · exact cliqueFree_three
end Mycielski
