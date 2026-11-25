-- Prove2me | solution 1 for ListEdgeColouring.gale_shapley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:51:37.901421+00:00
-- url     : https://prove2.me/submissions/14cd0a74-9e28-4e56-96fd-5265a11edf35

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_Galvin_gale_shapley


set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring
namespace ListEdgeColouring
theorem _root_.solution {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) :=
  Galvin.gale_shapley E rm rw hrm hrw
end ListEdgeColouring
