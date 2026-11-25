-- Prove2me | solution 1 for Mycielski.colorable_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:03.241679+00:00
-- url     : https://prove2.me/submissions/ddd90682-aa13-4419-98e1-cd9ceaffc842

module
public import Definitions.Def_Mycielski_Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_Mycielski_Coloring

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u v
namespace Mycielski
theorem _root_.solution {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (h : G.Colorable k) : (graph G).Colorable (k + 1) := by
  obtain ⟨c⟩ := h
  exact ⟨(graph G).recolorOfEquiv (finSuccEquiv k).symm (liftColoring c)⟩
end Mycielski
