-- Prove2me | solution 1 for Mycielski.not_shadow_adj_shadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:06.867927+00:00
-- url     : https://prove2.me/submissions/b7d0a293-ad3c-4c08-80c2-40c2b0933f5c

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
    ¬ (graph G).Adj (shadow v) (shadow w) := id
end Mycielski
