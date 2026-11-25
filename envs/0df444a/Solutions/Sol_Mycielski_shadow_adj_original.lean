-- Prove2me | solution 1 for Mycielski.shadow_adj_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:04.376795+00:00
-- url     : https://prove2.me/submissions/0110fb2d-95ef-40b5-b0b1-f4a14e5414e7

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
    (graph G).Adj (shadow v) (original w) ↔ G.Adj v w := Iff.rfl
end Mycielski
