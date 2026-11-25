-- Prove2me | solution 1 for Mycielski.cliqueFree_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:16.316901+00:00
-- url     : https://prove2.me/submissions/4ab792ac-ddc1-47b2-85bd-5b60c3c36b10

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
theorem _root_.solution {V : Type u} (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ v w z, G.Adj v w → G.Adj v z → ¬ G.Adj w z := by
  classical
  constructor
  · intro h v w z hvw hvz hwz
    exact h {v, w, z} (is3Clique_triple_iff.mpr ⟨hvw, hvz, hwz⟩)
  · intro h s hs
    obtain ⟨v, w, z, hvw, hvz, hwz, _⟩ := is3Clique_iff.mp hs
    exact h v w z hvw hvz hwz
end Mycielski
