-- Prove2me | solution 1 for Mycielski.original_adj_shadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:01.885637+00:00
-- url     : https://prove2.me/submissions/793fd188-70f2-469b-8141-b9f4208805f4

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
    (graph G).Adj (original v) (shadow w) ↔ G.Adj v w := Iff.rfl
end Mycielski
