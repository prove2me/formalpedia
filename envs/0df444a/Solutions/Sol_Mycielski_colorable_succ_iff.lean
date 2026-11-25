-- Prove2me | solution 1 for Mycielski.colorable_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:40.960885+00:00
-- url     : https://prove2.me/submissions/13fd77d7-6b7c-41c5-940b-dd6aee685b6c

module
public import Definitions.Def_Mycielski_Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_Mycielski_Coloring
public import Theorems.Thm_Mycielski_colorable_succ
public import Theorems.Thm_Mycielski_colorable_of_colorable_succ

set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
universe u v
namespace Mycielski
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (k : ℕ) :
    (graph G).Colorable (k + 1) ↔ G.Colorable k :=
  ⟨colorable_of_colorable_succ, colorable_succ⟩
end Mycielski
