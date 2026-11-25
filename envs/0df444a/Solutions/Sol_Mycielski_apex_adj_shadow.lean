-- Prove2me | solution 1 for Mycielski.apex_adj_shadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:15.284247+00:00
-- url     : https://prove2.me/submissions/ad052f34-7319-4a3e-91f6-18aa004547d5

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
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (v : V) :
    (graph G).Adj none (shadow v) := trivial
end Mycielski
