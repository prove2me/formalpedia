-- Prove2me | solution 1 for Mycielski.original_adj_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:58.975638+00:00
-- url     : https://prove2.me/submissions/bcfe5d5b-829e-43d5-8cd1-e558807f07be

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Mycielski_Basic

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u
namespace Mycielski
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (v w : V) :
    (graph G).Adj (original v) (original w) ↔ G.Adj v w := Iff.rfl
end Mycielski
