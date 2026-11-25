-- Prove2me | solution 1 for Mycielski.shadow_adj_apex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:12.408903+00:00
-- url     : https://prove2.me/submissions/acd931cb-53f0-4637-9b34-4553a0a27161

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
    (graph G).Adj (shadow v) none := trivial
end Mycielski
