-- Prove2me | solution 1 for Mycielski.colorable_of_colorable_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:51.184933+00:00
-- url     : https://prove2.me/submissions/a3b75bd6-8696-491e-9a16-864014a51a1c

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
    (h : (graph G).Colorable (k + 1)) : G.Colorable k := by
  obtain ⟨c⟩ := h
  exact ⟨G.recolorOfEquiv (finSuccAboveEquiv (c none)).symm (lowerColoring c)⟩
end Mycielski
